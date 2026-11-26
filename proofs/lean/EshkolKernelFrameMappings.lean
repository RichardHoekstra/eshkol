/-
  EshkolKernelFrameMappings.lean
  The composition of the K2 frame pool and address spaces of tsotchke/eshkol
  (lib/kernel/k2_mmu_frames.c), with native's status codes and check order.

  Hidden decision: the actual mapping relation is a global list of entries
  (space, page, frame, permissions). Native's slot arrays, PTE encoding, TLB and
  page-table capacity are abstracted away. The x86-64 encoding is reduced to the
  one check it adds after the permission policy: a kernel-space entry must not
  carry the user bit. Page-table exhaustion (512 entries) and non-canonical or
  misaligned addresses are outside the model.

  Native also keeps three per-frame summaries of the relation. They are modelled
  as recorded fields, separate from the relation itself:
    refcount   exact      the number of entries that reference the frame
    permUnion  covering   a superset of the permissions of those entries
    lastAsid   sound      the ASID of the last space to map the frame
  Each summary has its own named relation to the actual entries below.

  Each entry also carries a ghost field, the frame generation at mapping time,
  which native does not store. It expresses temporal safety.

  Invariants (named separately; Coherent is their conjunction):
    RefcountExact, ReferentialIntegrity, KernelFramesNotInUser,
    EntriesSatisfyPolicy, PermUnionCovers, NoWriteExecuteAlias,
    GenerationCurrent, PageUnique, LastAsidSound, UserAsidsAgree.
  Environmental assumption, separate: UniqueAsids (native does not enforce it).
  Guarantee: UniqueAsids ∧ Coherent → MutableIsolation, where MutableIsolation
  forbids a frame mapped in two user ASIDs if either mapping is writable.
  Native's rule is stricter (SingleUserAsid: no read-only sharing either); that
  is a precision property of native, not the guarantee.
-/

namespace EshkolKernelFrameMappings

inductive Owner where
  | free | kernel | user
  deriving DecidableEq, Repr

structure Perms where
  r : Bool
  w : Bool
  x : Bool
  u : Bool
  k : Bool
  deriving DecidableEq, Repr

def Perms.empty : Perms := ⟨false, false, false, false, false⟩
def Perms.rwx (p : Perms) : Perms := ⟨p.r, p.w, p.x, false, false⟩
def Perms.union (a b : Perms) : Perms := ⟨a.r || b.r, a.w || b.w, a.x || b.x, false, false⟩

inductive Status where
  | ok | invalidArg | outOfFrames | doubleFree | staleHandle | kernelFrameLocked
  | frameStillMapped | wxViolation | privViolation | kernelAlias | permAlias
  | vaAlreadyMapped | vaNotMapped
  deriving DecidableEq, Repr

/-- Native `k2_check_perm_policy`. -/
def policy (p : Perms) (userSpace : Bool) : Status :=
  if p.w && p.x then .wxViolation
  else if p.u && p.k then .privViolation
  else if !(p.r || p.w || p.x) then .invalidArg
  else if p.w && !p.r then .invalidArg
  else if userSpace && (p.k || !p.u) then .privViolation
  else .ok

/-- What native's x86-64 encode and validate add once the policy has passed. -/
def encodeCheck (p : Perms) (userSpace : Bool) : Status :=
  if !userSpace && p.u then .privViolation else .ok

structure Frame where
  owner      : Owner
  generation : Nat
  refcount   : Nat
  permUnion  : Perms
  lastAsid   : Option Nat
  deriving DecidableEq, Repr

structure Space where
  asid : Nat
  user : Bool
  deriving DecidableEq, Repr

structure Entry where
  space      : Nat
  page       : Nat
  frame      : Nat
  perms      : Perms
  generation : Nat
  deriving DecidableEq, Repr

structure Handle where
  idx    : Nat
  gen    : Nat
  physOk : Bool
  deriving DecidableEq, Repr

structure System where
  total     : Nat
  freeCount : Nat
  allocated : Nat
  frames    : Nat → Frame
  spaces    : List Space
  entries   : List Entry

def setFrame (f : Nat → Frame) (i : Nat) (v : Frame) : Nat → Frame :=
  fun j => if j = i then v else f j

def System.init (total kernelReserved : Nat) (spaces : List Space) : System :=
  { total, freeCount := total - kernelReserved, allocated := kernelReserved,
    frames := fun i => ⟨if i < kernelReserved then .kernel else .free, 1, 0, Perms.empty, none⟩,
    spaces, entries := [] }

def Entry.at (s page : Nat) (e : Entry) : Bool := e.space == s && e.page == page

/-- The entry after remapping (s, page) to permissions p. -/
def remapEntry (s page : Nat) (p : Perms) (e : Entry) : Entry :=
  if Entry.at s page e then { e with perms := p } else e

/-- Native's frame summaries after one mapping of the frame is removed. -/
def Frame.release (f : Frame) : Frame :=
  if f.refcount = 0 then f
  else if f.refcount = 1 then { f with refcount := 0, permUnion := Perms.empty, lastAsid := none }
  else { f with refcount := f.refcount - 1 }

/-- `k2_frame_alloc_user` / `k2_frame_alloc_kernel` at the frame native chose. -/
def System.alloc (S : System) (o : Owner) (i : Nat) : Status × System :=
  if i < S.total ∧ (S.frames i).owner = .free ∧ 0 < S.freeCount then
    (.ok, { S with freeCount := S.freeCount - 1, allocated := S.allocated + 1,
                   frames := setFrame S.frames i
                     ⟨o, (S.frames i).generation + 1, 0, Perms.empty, none⟩ })
  else (.outOfFrames, S)

/-- `k2_frame_free_user`. -/
def System.free (S : System) (h : Handle) : Status × System :=
  if S.total ≤ h.idx then (.invalidArg, S)
  else
    let f := S.frames h.idx
    if f.owner = .kernel then (.kernelFrameLocked, S)
    else if f.owner = .free then (.doubleFree, S)
    else if h.gen ≠ f.generation then (.staleHandle, S)
    else if h.physOk = false then (.staleHandle, S)
    else if f.refcount ≠ 0 then (.frameStillMapped, S)
    else (.ok, { S with freeCount := S.freeCount + 1, allocated := S.allocated - 1,
                        frames := setFrame S.frames h.idx
                          ⟨.free, f.generation + 1, f.refcount, Perms.empty, none⟩ })

/-- `k2_aspace_map`. -/
def System.map (S : System) (s page : Nat) (h : Handle) (p : Perms) : Status × System :=
  match S.spaces[s]? with
  | none => (.invalidArg, S)
  | some sp =>
    if policy p sp.user ≠ .ok then (policy p sp.user, S)
    else if S.total ≤ h.idx then (.invalidArg, S)
    else
      let f := S.frames h.idx
      if f.owner = .kernel ∧ sp.user = true then (.kernelAlias, S)
      else if f.owner = .free then (.staleHandle, S)
      else if h.gen ≠ f.generation then (.staleHandle, S)
      else if h.physOk = false then (.staleHandle, S)
      else if 0 < f.refcount ∧ ((f.permUnion.w && p.x) || (f.permUnion.x && p.w)) = true then
        (.permAlias, S)
      else if 0 < f.refcount ∧ sp.user = true ∧ f.lastAsid ≠ none ∧ f.lastAsid ≠ some sp.asid then
        (.permAlias, S)
      else if S.entries.any (Entry.at s page) then (.vaAlreadyMapped, S)
      else if encodeCheck p sp.user ≠ .ok then (encodeCheck p sp.user, S)
      else (.ok, { S with
        entries := S.entries ++ [⟨s, page, h.idx, p, f.generation⟩],
        frames := setFrame S.frames h.idx
          { f with refcount := f.refcount + 1, permUnion := f.permUnion.union p.rwx,
                   lastAsid := some sp.asid } })

/-- `k2_aspace_remap_perms`. -/
def System.remap (S : System) (s page : Nat) (p : Perms) : Status × System :=
  match S.spaces[s]? with
  | none => (.invalidArg, S)
  | some sp =>
    if policy p sp.user ≠ .ok then (policy p sp.user, S)
    else
      match S.entries.find? (Entry.at s page) with
      | none => (.vaNotMapped, S)
      | some e =>
        let f := S.frames e.frame
        if 1 < f.refcount ∧ ((f.permUnion.w && p.x) || (f.permUnion.x && p.w)) = true then
          (.permAlias, S)
        else if encodeCheck p sp.user ≠ .ok then (encodeCheck p sp.user, S)
        else (.ok, { S with
          entries := S.entries.map (remapEntry s page p),
          frames := setFrame S.frames e.frame
            { f with permUnion := if f.refcount = 1 then p.rwx else f.permUnion.union p.rwx } })

/-- `k2_aspace_unmap`. -/
def System.unmap (S : System) (s page : Nat) : Status × System :=
  match S.entries.find? (Entry.at s page) with
  | none => (.vaNotMapped, S)
  | some e =>
    (.ok, { S with entries := S.entries.filter (fun e' => !Entry.at s page e'),
                   frames := setFrame S.frames e.frame (S.frames e.frame).release })

inductive Op where
  | alloc (o : Owner) (i : Nat)
  | free (h : Handle)
  | map (s page : Nat) (h : Handle) (p : Perms)
  | remap (s page : Nat) (p : Perms)
  | unmap (s page : Nat)

def System.step (S : System) : Op → Status × System
  | .alloc o i => S.alloc o i
  | .free h => S.free h
  | .map s page h p => S.map s page h p
  | .remap s page p => S.remap s page p
  | .unmap s page => S.unmap s page

/-! ## The actual relation and native's summaries -/

def System.mappings (S : System) (i : Nat) : Nat := S.entries.countP (fun e => e.frame == i)

def System.spaceOf (S : System) (e : Entry) : Option Space := S.spaces[e.space]?

def System.RefcountExact (S : System) : Prop :=
  ∀ i, (S.frames i).refcount = S.mappings i

def System.ReferentialIntegrity (S : System) : Prop :=
  ∀ e ∈ S.entries, e.frame < S.total ∧ (S.frames e.frame).owner ≠ .free

def System.KernelFramesNotInUser (S : System) : Prop :=
  ∀ e ∈ S.entries, ∀ sp, S.spaceOf e = some sp → sp.user = true →
    (S.frames e.frame).owner ≠ .kernel

def System.EntriesSatisfyPolicy (S : System) : Prop :=
  ∀ e ∈ S.entries, ∃ sp, S.spaceOf e = some sp ∧
    policy e.perms sp.user = .ok ∧ encodeCheck e.perms sp.user = .ok

def System.PermUnionCovers (S : System) : Prop :=
  ∀ e ∈ S.entries, (e.perms.w = true → (S.frames e.frame).permUnion.w = true) ∧
    (e.perms.x = true → (S.frames e.frame).permUnion.x = true)

def System.NoWriteExecuteAlias (S : System) : Prop :=
  ∀ a ∈ S.entries, ∀ b ∈ S.entries, a.frame = b.frame → ¬ (a.perms.w = true ∧ b.perms.x = true)

def System.GenerationCurrent (S : System) : Prop :=
  ∀ e ∈ S.entries, e.generation = (S.frames e.frame).generation

def System.PageUnique (S : System) : Prop :=
  S.entries.Pairwise (fun a b => ¬ (a.space = b.space ∧ a.page = b.page))

/-- The last-ASID summary is sound: for every user mapping of a frame, the recorded
    ASID is that mapping's ASID or the ASID of some kernel space. -/
def System.LastAsidSound (S : System) : Prop :=
  ∀ e ∈ S.entries, ∀ sp, S.spaceOf e = some sp → sp.user = true →
    ∃ a, (S.frames e.frame).lastAsid = some a ∧
      (a = sp.asid ∨ ∃ ks ∈ S.spaces, ks.user = false ∧ ks.asid = a)

/-- Two ASIDs agree, or one of them is also the ASID of a kernel space. -/
def System.AsidsCompatible (S : System) (x y : Nat) : Prop :=
  x = y ∨ ∃ ks ∈ S.spaces, ks.user = false ∧ (ks.asid = x ∨ ks.asid = y)

/-- Two user mappings of one frame lie in one ASID, unless a kernel space shares one
    of their ASIDs. Native's last-ASID check maintains this; LastAsidSound alone does
    not imply it, because a kernel-space last ASID says nothing about the user pair. -/
def System.UserAsidsAgree (S : System) : Prop :=
  ∀ a ∈ S.entries, ∀ b ∈ S.entries, ∀ sa sb, S.spaceOf a = some sa → S.spaceOf b = some sb →
    sa.user = true → sb.user = true → a.frame = b.frame → S.AsidsCompatible sa.asid sb.asid

def System.Coherent (S : System) : Prop :=
  S.RefcountExact ∧ S.ReferentialIntegrity ∧ S.KernelFramesNotInUser ∧
  S.EntriesSatisfyPolicy ∧ S.PermUnionCovers ∧ S.NoWriteExecuteAlias ∧
  S.GenerationCurrent ∧ S.PageUnique ∧ S.LastAsidSound ∧ S.UserAsidsAgree

/-- Environmental assumption: native does not enforce it. -/
def System.UniqueAsids (S : System) : Prop :=
  S.spaces.Pairwise (fun a b => a.asid ≠ b.asid)

/-- The guarantee: no frame is mapped in two user ASIDs if either mapping is writable. -/
def System.MutableIsolation (S : System) : Prop :=
  ∀ a ∈ S.entries, ∀ b ∈ S.entries, ∀ sa sb, S.spaceOf a = some sa → S.spaceOf b = some sb →
    sa.user = true → sb.user = true → a.frame = b.frame → sa.asid ≠ sb.asid →
    a.perms.w = false ∧ b.perms.w = false

/-- Native's stricter behaviour: a frame's user mappings all lie in one ASID. -/
def System.SingleUserAsid (S : System) : Prop :=
  ∀ a ∈ S.entries, ∀ b ∈ S.entries, ∀ sa sb, S.spaceOf a = some sa → S.spaceOf b = some sb →
    sa.user = true → sb.user = true → a.frame = b.frame → sa.asid = sb.asid

/-! ## Helper lemmas -/

theorem setFrame_apply (f : Nat → Frame) (i : Nat) (v : Frame) (j : Nat) :
    setFrame f i v j = if j = i then v else f j := rfl

theorem mappings_eq_zero (S : System) (i : Nat) :
    S.mappings i = 0 ↔ ∀ e ∈ S.entries, e.frame ≠ i := by
  unfold System.mappings
  rw [List.countP_eq_zero]
  simp

theorem refcount_pos_of_mem (S : System) (hR : S.RefcountExact) (e : Entry) (he : e ∈ S.entries) :
    0 < (S.frames e.frame).refcount := by
  rw [hR e.frame]
  unfold System.mappings
  exact (List.countP_pos (p := fun x => x.frame == e.frame)).mpr ⟨e, he, by simp⟩

theorem two_le_countP {α : Type} (q : α → Bool) : ∀ (l : List α) (a b : α), a ∈ l → b ∈ l →
    a ≠ b → q a = true → q b = true → 2 ≤ l.countP q
  | [], _, _, ha, _, _, _, _ => absurd ha (List.not_mem_nil _)
  | x :: t, a, b, ha, hb, hne, hqa, hqb => by
    rw [List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · have := (List.countP_pos (p := q)).mpr ⟨b, hb', hqb⟩
        simp [hqa]; omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have := (List.countP_pos (p := q)).mpr ⟨a, ha', hqa⟩
        simp [hqb]; omega
      · have := two_le_countP q t a b ha' hb' hne hqa hqb
        split <;> omega

/-- Removing the unique element with a given key lowers every count by that element's share. -/
theorem countP_filter_unique {α : Type} (q key : α → Bool) : ∀ (l : List α) (e : α), e ∈ l →
    key e = true → l.Pairwise (fun a b => ¬ (key a = true ∧ key b = true)) →
    (l.filter (fun x => !key x)).countP q + (if q e then 1 else 0) = l.countP q
  | [], _, he, _, _ => absurd he (List.not_mem_nil _)
  | x :: t, e, he, hk, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, ht⟩ := hp
    rcases List.mem_cons.mp he with rfl | he'
    · have hrest : ∀ y ∈ t, key y = false := by
        intro y hy
        cases hky : key y
        · rfl
        · exact absurd ⟨hk, hky⟩ (hx y hy)
      have hf : t.filter (fun x => !key x) = t :=
        List.filter_eq_self.mpr (fun y hy => by simp [hrest y hy])
      simp [List.filter_cons, hk, hf, List.countP_cons]
    · have hkx : key x = false := by
        cases hkx : key x
        · rfl
        · exact absurd ⟨hkx, hk⟩ (hx e he')
      have ih := countP_filter_unique q key t e he' hk ht
      simp only [List.filter_cons, hkx, Bool.not_false, if_true, List.countP_cons]
      omega

theorem policy_ok_not_wx (p : Perms) (u : Bool) (h : policy p u = .ok) :
    ¬ (p.w = true ∧ p.x = true) := by
  rintro ⟨hw, hx⟩
  simp [policy, hw, hx] at h

theorem pageUnique_key (S : System) (hU : S.PageUnique) (s page : Nat) :
    S.entries.Pairwise (fun a b => ¬ (Entry.at s page a = true ∧ Entry.at s page b = true)) :=
  hU.imp (fun {a b} hab hk => hab ⟨by
      simp [Entry.at] at hk; omega, by simp [Entry.at] at hk; omega⟩)

/-- Changing frame `i`, which no entry references, to a frame with no mappings. -/
theorem coherent_of_untouched (S : System) (i : Nat) (v : Frame) (fc al : Nat)
    (h : S.Coherent) (hnone : ∀ e ∈ S.entries, e.frame ≠ i) (hv : v.refcount = 0) :
    ({ S with freeCount := fc, allocated := al, frames := setFrame S.frames i v } : System).Coherent := by
  obtain ⟨hR, hI, hK, hP, hC, hW, hG, hU, hL, hA⟩ := h
  have same : ∀ e ∈ S.entries, setFrame S.frames i v e.frame = S.frames e.frame :=
    fun e he => by simp [setFrame_apply, hnone e he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA⟩
  · intro j
    show (setFrame S.frames i v j).refcount = S.mappings j
    by_cases hj : j = i
    · subst hj
      rw [setFrame_apply, if_pos rfl, hv]
      exact ((mappings_eq_zero S j).mpr hnone).symm
    · rw [setFrame_apply, if_neg hj]; exact hR j
  · intro e he; dsimp only at he ⊢; rw [same e he]; exact hI e he
  · intro e he sp hs hu; dsimp only at he ⊢; rw [same e he]; exact hK e he sp hs hu
  · exact hP
  · intro e he; dsimp only at he ⊢; rw [same e he]; exact hC e he
  · exact hW
  · intro e he; dsimp only at he ⊢; rw [same e he]; exact hG e he
  · exact hU
  · intro e he sp hs hu; dsimp only at he ⊢; rw [same e he]; exact hL e he sp hs hu

/-! ## Preservation of Coherent by every operation -/

theorem alloc_preserves (S : System) (o : Owner) (i : Nat) (h : S.Coherent) :
    (S.alloc o i).2.Coherent := by
  unfold System.alloc
  split
  · rename_i hc
    obtain ⟨_, hfree, _⟩ := hc
    refine coherent_of_untouched S i _ _ _ h ?_ rfl
    intro e he heq
    have := (h.2.1 e he).2
    rw [heq] at this
    exact this hfree
  · exact h

theorem free_preserves (S : System) (hd : Handle) (h : S.Coherent) : (S.free hd).2.Coherent := by
  unfold System.free
  split
  · exact h
  dsimp only
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  rename_i hrc
  have hz : (S.frames hd.idx).refcount = 0 := Decidable.of_not_not hrc
  refine coherent_of_untouched S hd.idx _ _ _ h ?_ hz
  have := h.1 hd.idx
  rw [hz] at this
  exact (mappings_eq_zero S hd.idx).mp this.symm

theorem asidsCompatible_symm {S : System} {x y : Nat} (h : S.AsidsCompatible x y) :
    S.AsidsCompatible y x := by
  rcases h with h | ⟨ks, hks, hku, h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨ks, hks, hku, h.symm⟩

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil _)
  | x :: t, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hne
    · exact Or.inl (hp.1 b hb')
    · exact Or.inr (hp.1 a ha')
    · exact pairwise_mem_ne hp.2 ha' hb' hne

theorem setFrame_owner (f : Nat → Frame) (i : Nat) (rc : Nat) (pu : Perms) (la : Option Nat) (j : Nat) :
    (setFrame f i { f i with refcount := rc, permUnion := pu, lastAsid := la } j).owner = (f j).owner := by
  unfold setFrame; split <;> simp_all

theorem setFrame_generation (f : Nat → Frame) (i : Nat) (rc : Nat) (pu : Perms) (la : Option Nat) (j : Nat) :
    (setFrame f i { f i with refcount := rc, permUnion := pu, lastAsid := la } j).generation =
      (f j).generation := by
  unfold setFrame; split <;> simp_all

theorem map_preserves (S : System) (s page : Nat) (hd : Handle) (p : Perms) (h : S.Coherent) :
    (S.map s page hd p).2.Coherent := by
  unfold System.map
  cases hsp : S.spaces[s]? with
  | none => exact h
  | some sp =>
  dsimp only
  by_cases hpol : policy p sp.user ≠ .ok
  · rw [if_pos hpol]; exact h
  rw [if_neg hpol]
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  by_cases henc : encodeCheck p sp.user ≠ .ok
  · rw [if_pos henc]; exact h
  rw [if_neg henc]
  rename_i hlt hka hfr _ _ hwx has hva
  obtain ⟨hR, hI, hK, hP, hC, hW, hG, hU, hL, hA⟩ := h
  have hpol' : policy p sp.user = .ok := Decidable.of_not_not hpol
  have henc' : encodeCheck p sp.user = .ok := Decidable.of_not_not henc
  have hlt' : hd.idx < S.total := Nat.lt_of_not_le hlt
  have hmem_sp : sp ∈ S.spaces := List.getElem?_mem hsp
  have space_new : ∀ sp', S.spaces[s]? = some sp' → sp' = sp := by
    intro sp' hs; rw [hsp] at hs; exact (Option.some.inj hs).symm
  have newCompat : ∀ a ∈ S.entries, ∀ sa, S.spaceOf a = some sa → sa.user = true →
      sp.user = true → a.frame = hd.idx → S.AsidsCompatible sa.asid sp.asid := by
    intro a ha sa hsa hua hspu haf
    obtain ⟨x, hx, hor⟩ := hL a ha sa hsa hua
    rw [haf] at hx
    have hrc := refcount_pos_of_mem S hR a ha
    rw [haf] at hrc
    have hlast : (S.frames hd.idx).lastAsid = some sp.asid :=
      Decidable.byContradiction fun hne => has ⟨hrc, hspu, by rw [hx]; simp, hne⟩
    rw [hx] at hlast
    have hxs : x = sp.asid := Option.some.inj hlast
    subst hxs
    rcases hor with h | ⟨ks, hks, hku, hka⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨ks, hks, hku, Or.inr hka⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- RefcountExact
    intro j
    dsimp only [System.mappings]
    rw [List.countP_append, setFrame_apply]
    by_cases hj : j = hd.idx
    · subst hj; simp [hR hd.idx, System.mappings]
    · have hne : hd.idx ≠ j := fun h => hj h.symm
      simp [hj, hne, hR j, System.mappings]
  · -- ReferentialIntegrity
    intro e he
    dsimp only at he ⊢
    rw [setFrame_owner]
    rcases List.mem_append.mp he with he | he
    · exact hI e he
    · rw [List.mem_singleton] at he; subst he; exact ⟨hlt', hfr⟩
  · -- KernelFramesNotInUser
    intro e he sp' hs hu
    dsimp only at he ⊢
    rw [setFrame_owner]
    rcases List.mem_append.mp he with he | he
    · exact hK e he sp' hs hu
    · rw [List.mem_singleton] at he; subst he
      have := space_new sp' hs; subst this
      exact fun hk => hka ⟨hk, hu⟩
  · -- EntriesSatisfyPolicy
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hP e he
    · rw [List.mem_singleton] at he; subst he; exact ⟨sp, hsp, hpol', henc'⟩
  · -- PermUnionCovers
    intro e he
    dsimp only at he ⊢
    rw [setFrame_apply]
    by_cases hj : e.frame = hd.idx
    · rw [if_pos hj]
      rcases List.mem_append.mp he with he | he
      · have := hC e he; rw [hj] at this
        simp only [Perms.union, Perms.rwx]
        exact ⟨fun hw => by simp [this.1 hw], fun hx => by simp [this.2 hx]⟩
      · rw [List.mem_singleton] at he; subst he
        exact ⟨fun hw => by simp only [Perms.union, Perms.rwx, Bool.or_eq_true]; exact Or.inr hw,
               fun hx => by simp only [Perms.union, Perms.rwx, Bool.or_eq_true]; exact Or.inr hx⟩
    · rw [if_neg hj]
      rcases List.mem_append.mp he with he | he
      · exact hC e he
      · rw [List.mem_singleton] at he; subst he; exact absurd rfl hj
  · -- NoWriteExecuteAlias
    intro a ha b hb hab
    dsimp only at ha hb
    have unionOf : ∀ e ∈ S.entries, e.frame = hd.idx →
        (e.perms.w = true → (S.frames hd.idx).permUnion.w = true) ∧
        (e.perms.x = true → (S.frames hd.idx).permUnion.x = true) ∧
        0 < (S.frames hd.idx).refcount := by
      intro e he hj
      have hc := hC e he; have hr := refcount_pos_of_mem S hR e he
      rw [hj] at hc hr; exact ⟨hc.1, hc.2, hr⟩
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact hW a ha b hb hab
    · rw [List.mem_singleton] at hb; subst hb
      rintro ⟨haw, hpx⟩
      have hpx' : p.x = true := hpx
      obtain ⟨hcw, _, hr⟩ := unionOf a ha hab
      exact hwx ⟨hr, by simp [hcw haw, hpx']⟩
    · rw [List.mem_singleton] at ha; subst ha
      rintro ⟨hpw, hbx⟩
      have hpw' : p.w = true := hpw
      obtain ⟨_, hcx, hr⟩ := unionOf b hb hab.symm
      exact hwx ⟨hr, by simp [hcx hbx, hpw']⟩
    · rw [List.mem_singleton] at ha hb; subst ha; subst hb
      exact policy_ok_not_wx p sp.user hpol'
  · -- GenerationCurrent
    intro e he
    dsimp only at he ⊢
    rw [setFrame_generation]
    rcases List.mem_append.mp he with he | he
    · exact hG e he
    · rw [List.mem_singleton] at he; subst he; rfl
  · -- PageUnique
    show (S.entries ++ _).Pairwise _
    rw [List.pairwise_append]
    refine ⟨hU, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    rintro ⟨h1, h2⟩
    exact hva (List.any_eq_true.mpr ⟨a, ha, by simp [Entry.at, h1, h2]⟩)
  · -- LastAsidSound
    intro e he sp' hs hu
    dsimp only at he ⊢
    rw [setFrame_apply]
    by_cases hj : e.frame = hd.idx
    · rw [if_pos hj]
      refine ⟨sp.asid, rfl, ?_⟩
      rcases List.mem_append.mp he with he | he
      · cases hsu : sp.user
        · exact Or.inr ⟨sp, hmem_sp, hsu, rfl⟩
        · obtain ⟨a, ha, hor⟩ := hL e he sp' hs hu
          rw [hj] at ha
          have hrc := refcount_pos_of_mem S hR e he
          rw [hj] at hrc
          have hlast : (S.frames hd.idx).lastAsid = some sp.asid := by
            apply Decidable.byContradiction
            intro hne
            exact has ⟨hrc, hsu, by rw [ha]; simp, hne⟩
          rw [ha] at hlast
          have hasid : a = sp.asid := Option.some.inj hlast
          subst hasid
          exact hor
      · rw [List.mem_singleton] at he; subst he
        have := space_new sp' hs; subst this
        exact Or.inl rfl
    · rw [if_neg hj]
      rcases List.mem_append.mp he with he | he
      · exact hL e he sp' hs hu
      · rw [List.mem_singleton] at he; subst he; exact absurd rfl hj
  · -- UserAsidsAgree
    intro a ha b hb sa sb hsa hsb hua hub hab
    dsimp only at ha hb
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact hA a ha b hb sa sb hsa hsb hua hub hab
    · rw [List.mem_singleton] at hb; subst hb
      have := space_new sb hsb; subst this
      exact newCompat a ha sa hsa hua hub hab
    · rw [List.mem_singleton] at ha; subst ha
      have := space_new sa hsa; subst this
      exact asidsCompatible_symm (newCompat b hb sb hsb hub hua hab.symm)
    · rw [List.mem_singleton] at ha hb; subst ha; subst hb
      have h1 := space_new sa hsa; have h2 := space_new sb hsb
      subst h1; subst h2; exact Or.inl rfl

/-! ## Remap and unmap -/

theorem remapEntry_frame (s page : Nat) (p : Perms) (y : Entry) : (remapEntry s page p y).frame = y.frame := by
  by_cases hk : Entry.at s page y = true <;> simp [remapEntry, hk]
theorem remapEntry_space (s page : Nat) (p : Perms) (y : Entry) : (remapEntry s page p y).space = y.space := by
  by_cases hk : Entry.at s page y = true <;> simp [remapEntry, hk]
theorem remapEntry_page (s page : Nat) (p : Perms) (y : Entry) : (remapEntry s page p y).page = y.page := by
  by_cases hk : Entry.at s page y = true <;> simp [remapEntry, hk]
theorem remapEntry_generation (s page : Nat) (p : Perms) (y : Entry) :
    (remapEntry s page p y).generation = y.generation := by
  by_cases hk : Entry.at s page y = true <;> simp [remapEntry, hk]
theorem remapEntry_perms (s page : Nat) (p : Perms) (y : Entry) :
    (remapEntry s page p y).perms = if Entry.at s page y then p else y.perms := by
  by_cases hk : Entry.at s page y = true <;> simp [remapEntry, hk]

theorem setFrame_pu_owner (f : Nat → Frame) (i : Nat) (U : Perms) (j : Nat) :
    (setFrame f i { f i with permUnion := U } j).owner = (f j).owner := by
  unfold setFrame; split <;> simp_all
theorem setFrame_pu_generation (f : Nat → Frame) (i : Nat) (U : Perms) (j : Nat) :
    (setFrame f i { f i with permUnion := U } j).generation = (f j).generation := by
  unfold setFrame; split <;> simp_all
theorem setFrame_pu_refcount (f : Nat → Frame) (i : Nat) (U : Perms) (j : Nat) :
    (setFrame f i { f i with permUnion := U } j).refcount = (f j).refcount := by
  unfold setFrame; split <;> simp_all
theorem setFrame_pu_lastAsid (f : Nat → Frame) (i : Nat) (U : Perms) (j : Nat) :
    (setFrame f i { f i with permUnion := U } j).lastAsid = (f j).lastAsid := by
  unfold setFrame; split <;> simp_all

theorem release_owner (f : Frame) : f.release.owner = f.owner := by
  unfold Frame.release; split <;> (try split) <;> rfl
theorem release_generation (f : Frame) : f.release.generation = f.generation := by
  unfold Frame.release; split <;> (try split) <;> rfl
theorem release_refcount (f : Frame) : f.release.refcount = f.refcount - 1 := by
  unfold Frame.release; split <;> (try split) <;> simp_all
theorem release_summaries (f : Frame) (h : f.refcount ≠ 1) :
    f.release.permUnion = f.permUnion ∧ f.release.lastAsid = f.lastAsid := by
  unfold Frame.release
  by_cases h0 : f.refcount = 0 <;> simp [h0, h]

theorem setFrame_release_owner (f : Nat → Frame) (i j : Nat) :
    (setFrame f i (f i).release j).owner = (f j).owner := by
  unfold setFrame; split <;> simp_all [release_owner]
theorem setFrame_release_generation (f : Nat → Frame) (i j : Nat) :
    (setFrame f i (f i).release j).generation = (f j).generation := by
  unfold setFrame; split <;> simp_all [release_generation]

theorem union_covers_new (c : Prop) [Decidable c] (old p : Perms) :
    (p.w = true → (if c then p.rwx else old.union p.rwx).w = true) ∧
    (p.x = true → (if c then p.rwx else old.union p.rwx).x = true) := by
  constructor <;> intro hh <;> split <;> simp [Perms.rwx, Perms.union, hh]

theorem countP_filter_unique_pos {α : Type} (q key : α → Bool) (l : List α) (e : α) (he : e ∈ l)
    (hk : key e = true) (hp : l.Pairwise (fun a b => ¬ (key a = true ∧ key b = true)))
    (hq : q e = true) : (l.filter (fun x => !key x)).countP q + 1 = l.countP q := by
  have h := countP_filter_unique q key l e he hk hp
  rw [hq] at h
  have h1 : (if true = true then 1 else 0) = 1 := rfl
  omega

theorem countP_filter_unique_neg {α : Type} (q key : α → Bool) (l : List α) (e : α) (he : e ∈ l)
    (hk : key e = true) (hp : l.Pairwise (fun a b => ¬ (key a = true ∧ key b = true)))
    (hq : q e = false) : (l.filter (fun x => !key x)).countP q = l.countP q := by
  have h := countP_filter_unique q key l e he hk hp
  rw [hq] at h
  have h0 : (if false = true then 1 else 0) = 0 := rfl
  omega

theorem remap_preserves (S : System) (s page : Nat) (p : Perms) (h : S.Coherent) :
    (S.remap s page p).2.Coherent := by
  unfold System.remap
  cases hsp : S.spaces[s]? with
  | none => exact h
  | some sp =>
  dsimp only
  by_cases hpol : policy p sp.user ≠ .ok
  · rw [if_pos hpol]; exact h
  rw [if_neg hpol]
  cases hfind : S.entries.find? (Entry.at s page) with
  | none => exact h
  | some e =>
  dsimp only
  split
  · exact h
  by_cases henc : encodeCheck p sp.user ≠ .ok
  · rw [if_pos henc]; exact h
  rw [if_neg henc]
  rename_i halias
  obtain ⟨hR, hI, hK, hP, hC, hW, hG, hU, hL, hA⟩ := h
  have hpol' : policy p sp.user = .ok := Decidable.of_not_not hpol
  have henc' : encodeCheck p sp.user = .ok := Decidable.of_not_not henc
  have he : e ∈ S.entries := List.mem_of_find?_eq_some hfind
  have hke : Entry.at s page e = true := List.find?_some hfind
  have hunique : ∀ y ∈ S.entries, Entry.at s page y = true → y = e := by
    intro y hy hky
    apply Decidable.byContradiction
    intro hne
    have h1 := hky; have h2 := hke
    simp [Entry.at] at h1 h2
    rcases pairwise_mem_ne hU hy he hne with hc | hc
    · exact hc ⟨by omega, by omega⟩
    · exact hc ⟨by omega, by omega⟩
  have hspace : ∀ y, S.spaceOf (remapEntry s page p y) = S.spaceOf y := fun y => by
    simp only [System.spaceOf, remapEntry_space]
  have conflict : ∀ y ∈ S.entries, Entry.at s page y = false → y.frame = e.frame →
      1 < (S.frames e.frame).refcount ∧
      (y.perms.w = true → (S.frames e.frame).permUnion.w = true) ∧
      (y.perms.x = true → (S.frames e.frame).permUnion.x = true) := by
    intro y hy hk hj
    have hne : y ≠ e := by
      intro h; rw [h, hke] at hk; exact Bool.noConfusion hk
    have h2 := two_le_countP (fun x : Entry => x.frame == e.frame) S.entries y e hy he hne
      (by simp [hj]) (by simp)
    have h3 := hR e.frame
    unfold System.mappings at h3
    have hcy := hC y hy
    rw [hj] at hcy
    exact ⟨by omega, hcy.1, hcy.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- RefcountExact
    intro j
    dsimp only [System.mappings]
    rw [setFrame_pu_refcount, hR j, System.mappings, List.countP_map]
    exact List.countP_congr (fun y _ => by simp [Function.comp, remapEntry_frame])
  · -- ReferentialIntegrity
    intro x hx
    dsimp only at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [remapEntry_frame, setFrame_pu_owner]
    exact hI y hy
  · -- KernelFramesNotInUser
    intro x hx sp' hs hu
    dsimp only at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [remapEntry_frame, setFrame_pu_owner]
    exact hK y hy sp' (by rw [← hspace y]; exact hs) hu
  · -- EntriesSatisfyPolicy
    intro x hx
    dsimp only at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    by_cases hk : Entry.at s page y = true
    · have hys : y.space = s := by simp [Entry.at] at hk; exact hk.1
      refine ⟨sp, ?_, ?_⟩
      · show S.spaces[(remapEntry s page p y).space]? = some sp
        rw [remapEntry_space, hys]; exact hsp
      · rw [remapEntry_perms, if_pos hk]; exact ⟨hpol', henc'⟩
    · obtain ⟨sp', h1, h2, h3⟩ := hP y hy
      refine ⟨sp', ?_, ?_⟩
      · show S.spaceOf (remapEntry s page p y) = some sp'
        rw [hspace]; exact h1
      · rw [remapEntry_perms, if_neg hk]; exact ⟨h2, h3⟩
  · -- PermUnionCovers
    intro x hx
    dsimp only at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [remapEntry_frame, remapEntry_perms, setFrame_apply]
    by_cases hj : y.frame = e.frame
    · rw [if_pos hj]
      dsimp only
      by_cases hk : Entry.at s page y = true
      · rw [if_pos hk]; exact union_covers_new _ _ _
      · rw [if_neg hk]
        obtain ⟨h1, hcw, hcx⟩ := conflict y hy (Bool.eq_false_iff.mpr hk) hj
        rw [if_neg (by omega)]
        exact ⟨fun hw => by simp [Perms.union, hcw hw], fun hx => by simp [Perms.union, hcx hx]⟩
    · rw [if_neg hj]
      by_cases hk : Entry.at s page y = true
      · exact absurd (congrArg Entry.frame (hunique y hy hk)) hj
      · rw [if_neg hk]; exact hC y hy
  · -- NoWriteExecuteAlias
    intro a ha b hb hab
    dsimp only at ha hb
    obtain ⟨ya, hya, rfl⟩ := List.mem_map.mp ha
    obtain ⟨yb, hyb, rfl⟩ := List.mem_map.mp hb
    rw [remapEntry_frame, remapEntry_frame] at hab
    rw [remapEntry_perms, remapEntry_perms]
    by_cases hka : Entry.at s page ya = true <;> by_cases hkb : Entry.at s page yb = true
    · rw [if_pos hka, if_pos hkb]; exact policy_ok_not_wx p sp.user hpol'
    · rw [if_pos hka, if_neg hkb]
      have hya' := hunique ya hya hka
      rintro ⟨hpw, hbx⟩
      obtain ⟨h1, _, hcx⟩ := conflict yb hyb (Bool.eq_false_iff.mpr hkb) (by rw [← hab, hya'])
      exact halias ⟨h1, by simp [hcx hbx, hpw]⟩
    · rw [if_neg hka, if_pos hkb]
      have hyb' := hunique yb hyb hkb
      rintro ⟨haw, hpx⟩
      obtain ⟨h1, hcw, _⟩ := conflict ya hya (Bool.eq_false_iff.mpr hka) (by rw [hab, hyb'])
      exact halias ⟨h1, by simp [hcw haw, hpx]⟩
    · rw [if_neg hka, if_neg hkb]; exact hW ya hya yb hyb hab
  · -- GenerationCurrent
    intro x hx
    dsimp only at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [remapEntry_generation, remapEntry_frame, setFrame_pu_generation]
    exact hG y hy
  · -- PageUnique
    show (S.entries.map (remapEntry s page p)).Pairwise _
    rw [List.pairwise_map]
    exact hU.imp (fun {a b} h => by
      rw [remapEntry_space, remapEntry_space, remapEntry_page, remapEntry_page]; exact h)
  · -- LastAsidSound
    intro x hx sp' hs hu
    dsimp only at hx ⊢
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [remapEntry_frame, setFrame_pu_lastAsid]
    exact hL y hy sp' (by rw [← hspace y]; exact hs) hu
  · -- UserAsidsAgree
    intro a ha b hb sa sb hsa hsb hua hub hab
    dsimp only at ha hb
    obtain ⟨ya, hya, rfl⟩ := List.mem_map.mp ha
    obtain ⟨yb, hyb, rfl⟩ := List.mem_map.mp hb
    rw [remapEntry_frame, remapEntry_frame] at hab
    exact hA ya hya yb hyb sa sb (by rw [← hspace ya]; exact hsa) (by rw [← hspace yb]; exact hsb)
      hua hub hab

theorem unmap_preserves (S : System) (s page : Nat) (h : S.Coherent) :
    (S.unmap s page).2.Coherent := by
  unfold System.unmap
  cases hfind : S.entries.find? (Entry.at s page) with
  | none => exact h
  | some e =>
  dsimp only
  obtain ⟨hR, hI, hK, hP, hC, hW, hG, hU, hL, hA⟩ := h
  have he : e ∈ S.entries := List.mem_of_find?_eq_some hfind
  have hke : Entry.at s page e = true := List.find?_some hfind
  have hkey := pageUnique_key S hU s page
  have hmem : ∀ x, x ∈ S.entries.filter (fun e' => !Entry.at s page e') → x ∈ S.entries :=
    fun x hx => (List.mem_filter.mp hx).1
  have hsurv : ∀ x ∈ S.entries.filter (fun e' => !Entry.at s page e'), x.frame = e.frame →
      (S.frames e.frame).refcount ≠ 1 := by
    intro x hx hj h1
    have hc := countP_filter_unique_pos (fun x : Entry => x.frame == e.frame) (Entry.at s page)
      S.entries e he hke hkey (by simp)
    have hpos := (List.countP_pos (p := fun x : Entry => x.frame == e.frame)).mpr ⟨x, hx, by simp [hj]⟩
    have h3 := hR e.frame
    unfold System.mappings at h3
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- RefcountExact
    intro j
    dsimp only [System.mappings]
    rw [setFrame_apply]
    by_cases hj : j = e.frame
    · rw [if_pos hj, release_refcount]
      subst hj
      have hc := countP_filter_unique_pos (fun x : Entry => x.frame == e.frame) (Entry.at s page)
        S.entries e he hke hkey (by simp)
      have h3 := hR e.frame
      unfold System.mappings at h3
      omega
    · rw [if_neg hj]
      have hc := countP_filter_unique_neg (fun x : Entry => x.frame == j) (Entry.at s page)
        S.entries e he hke hkey (by simp; exact fun h => hj h.symm)
      have h3 := hR j
      unfold System.mappings at h3
      omega
  · intro x hx
    dsimp only at hx ⊢
    rw [setFrame_release_owner]; exact hI x (hmem x hx)
  · intro x hx sp' hs hu
    dsimp only at hx ⊢
    rw [setFrame_release_owner]; exact hK x (hmem x hx) sp' hs hu
  · intro x hx; exact hP x (hmem x hx)
  · -- PermUnionCovers
    intro x hx
    dsimp only at hx ⊢
    rw [setFrame_apply]
    by_cases hj : x.frame = e.frame
    · rw [if_pos hj, (release_summaries _ (hsurv x hx hj)).1, ← hj]; exact hC x (hmem x hx)
    · rw [if_neg hj]; exact hC x (hmem x hx)
  · intro a ha b hb; exact hW a (hmem a ha) b (hmem b hb)
  · intro x hx
    dsimp only at hx ⊢
    rw [setFrame_release_generation]; exact hG x (hmem x hx)
  · exact List.Pairwise.filter _ hU
  · -- LastAsidSound
    intro x hx sp' hs hu
    dsimp only at hx ⊢
    rw [setFrame_apply]
    by_cases hj : x.frame = e.frame
    · rw [if_pos hj, (release_summaries _ (hsurv x hx hj)).2, ← hj]
      exact hL x (hmem x hx) sp' hs hu
    · rw [if_neg hj]; exact hL x (hmem x hx) sp' hs hu
  · intro a ha b hb; exact hA a (hmem a ha) b (hmem b hb)

/-! ## Reachability -/

theorem step_preserves_coherent (S : System) (op : Op) (h : S.Coherent) : (S.step op).2.Coherent := by
  cases op with
  | alloc o i => exact alloc_preserves S o i h
  | free hd => exact free_preserves S hd h
  | map s page hd p => exact map_preserves S s page hd p h
  | remap s page p => exact remap_preserves S s page p h
  | unmap s page => exact unmap_preserves S s page h

def System.run : System → List Op → System
  | S, [] => S
  | S, op :: ops => (S.step op).2.run ops

theorem run_preserves_coherent : ∀ (S : System) (ops : List Op), S.Coherent → (S.run ops).Coherent
  | _, [], h => h
  | S, op :: ops, h => run_preserves_coherent _ ops (step_preserves_coherent S op h)

theorem init_coherent (total kernelReserved : Nat) (spaces : List Space) :
    (System.init total kernelReserved spaces).Coherent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; simp [System.init, System.mappings]
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he
  · exact List.Pairwise.nil
  · intro e he; simp [System.init] at he
  · intro e he; simp [System.init] at he

/-- Every state reachable from an initial state is coherent, with or without unique ASIDs. -/
theorem reachable_coherent (total kernelReserved : Nat) (spaces : List Space) (ops : List Op) :
    ((System.init total kernelReserved spaces).run ops).Coherent :=
  run_preserves_coherent _ ops (init_coherent total kernelReserved spaces)

/-! ## Isolation: the guarantee, under the environmental assumption -/

theorem unique_asids_single_user_asid (S : System) (hu : S.UniqueAsids) (h : S.Coherent) :
    S.SingleUserAsid := by
  intro a ha b hb sa sb hsa hsb hua hub hab
  rcases h.2.2.2.2.2.2.2.2.2 a ha b hb sa sb hsa hsb hua hub hab with heq | ⟨ks, hks, hku, hka⟩
  · exact heq
  · exfalso
    have mem_of : ∀ x sx, S.spaceOf x = some sx → sx ∈ S.spaces := fun x sx hx => by
      unfold System.spaceOf at hx; exact List.getElem?_mem hx
    have clash : ∀ sx ∈ S.spaces, sx.user = true → ks.asid = sx.asid → False := by
      intro sx hsx hux hk
      have hne : ks ≠ sx := by intro h; rw [h, hux] at hku; exact Bool.noConfusion hku
      rcases pairwise_mem_ne hu hks hsx hne with hc | hc
      · exact hc hk
      · exact hc hk.symm
    rcases hka with hka | hka
    · exact clash sa (mem_of a sa hsa) hua hka
    · exact clash sb (mem_of b sb hsb) hub hka

/-- The guarantee: UniqueAsids ∧ Coherent → MutableIsolation. -/
theorem mutable_isolation (S : System) (hu : S.UniqueAsids) (h : S.Coherent) :
    S.MutableIsolation := by
  intro a ha b hb sa sb hsa hsb hua hub hab hne
  exact absurd (unique_asids_single_user_asid S hu h a ha b hb sa sb hsa hsb hua hub hab) hne


/-! ## The address-space table is fixed -/
theorem alloc_spaces (S : System) (o : Owner) (i : Nat) : (S.alloc o i).2.spaces = S.spaces := by
  unfold System.alloc; split <;> rfl
theorem free_spaces (S : System) (hd : Handle) : (S.free hd).2.spaces = S.spaces := by
  unfold System.free; dsimp only; repeat (first | rfl | split)
theorem map_spaces (S : System) (s page : Nat) (hd : Handle) (p : Perms) :
    (S.map s page hd p).2.spaces = S.spaces := by
  unfold System.map
  cases S.spaces[s]? with
  | none => rfl
  | some sp =>
    dsimp only
    by_cases hpol : policy p sp.user ≠ .ok
    · rw [if_pos hpol]
    rw [if_neg hpol]
    repeat (first | rfl | split)
    all_goals (by_cases henc : encodeCheck p sp.user ≠ .ok
               · rw [if_pos henc]
               · rw [if_neg henc])
theorem remap_spaces (S : System) (s page : Nat) (p : Perms) : (S.remap s page p).2.spaces = S.spaces := by
  unfold System.remap
  cases S.spaces[s]? with
  | none => rfl
  | some sp =>
    dsimp only
    by_cases hpol : policy p sp.user ≠ .ok
    · rw [if_pos hpol]
    rw [if_neg hpol]
    cases S.entries.find? (Entry.at s page) with
    | none => rfl
    | some e =>
      dsimp only
      split
      · rfl
      by_cases henc : encodeCheck p sp.user ≠ .ok
      · rw [if_pos henc]
      · rw [if_neg henc]
theorem unmap_spaces (S : System) (s page : Nat) : (S.unmap s page).2.spaces = S.spaces := by
  unfold System.unmap; split <;> rfl

theorem step_spaces (S : System) (op : Op) : (S.step op).2.spaces = S.spaces := by
  cases op
  · exact alloc_spaces ..
  · exact free_spaces ..
  · exact map_spaces ..
  · exact remap_spaces ..
  · exact unmap_spaces ..

theorem run_spaces : ∀ (S : System) (ops : List Op), (S.run ops).spaces = S.spaces
  | _, [] => rfl
  | S, op :: ops => (run_spaces _ ops).trans (step_spaces S op)

/-- Every reachable state satisfies MutableIsolation when the configured ASIDs are unique. -/
theorem reachable_mutable_isolation (total kernelReserved : Nat) (spaces : List Space)
    (ops : List Op) (hu : spaces.Pairwise (fun a b => a.asid ≠ b.asid)) :
    ((System.init total kernelReserved spaces).run ops).MutableIsolation := by
  apply mutable_isolation _ _ (reachable_coherent total kernelReserved spaces ops)
  show List.Pairwise _ ((System.init total kernelReserved spaces).run ops).spaces
  rw [run_spaces]; exact hu

/-! ## Necessity of the assumption, and a precision property of native -/

/-- Without UniqueAsids the guarantee fails: a kernel space sharing ASID 2 with user space 2
    lets user space 2 map writable a frame that user space 1 maps. Native reproduces this
    sequence (generate_frame_mapping_traces.c, configuration "collide"). -/
theorem asid_collision_breaks_isolation : ¬ ∀ (total kernelReserved : Nat) (spaces : List Space)
    (ops : List Op), ((System.init total kernelReserved spaces).run ops).MutableIsolation := by
  intro h
  have := h 1 0 [⟨2, false⟩, ⟨1, true⟩, ⟨2, true⟩]
    [.alloc .user 0,
     .map 1 2 ⟨0, 2, true⟩ ⟨true, false, false, true, false⟩,
     .map 0 0 ⟨0, 2, true⟩ ⟨true, false, false, false, true⟩,
     .map 2 5 ⟨0, 2, true⟩ ⟨true, true, false, true, false⟩]
    ⟨1, 2, 0, ⟨true, false, false, true, false⟩, 2⟩ (by decide)
    ⟨2, 5, 0, ⟨true, true, false, true, false⟩, 2⟩ (by decide)
    ⟨1, true⟩ ⟨2, true⟩ (by decide) (by decide) rfl rfl rfl (by decide)
  exact absurd this.2 (by decide)

/-- Precision: once a kernel space has mapped a frame, native refuses a read-only user
    mapping of it, although accepting would keep MutableIsolation and NoWriteExecuteAlias. -/
theorem kernel_last_asid_refuses_read_only_user :
    (((System.init 1 0 [⟨0, false⟩, ⟨1, true⟩]).run
        [.alloc .user 0, .map 0 0 ⟨0, 2, true⟩ ⟨true, false, false, false, true⟩]).map
      1 0 ⟨0, 2, true⟩ ⟨true, false, false, true, false⟩).1 = .permAlias := by decide

end EshkolKernelFrameMappings
