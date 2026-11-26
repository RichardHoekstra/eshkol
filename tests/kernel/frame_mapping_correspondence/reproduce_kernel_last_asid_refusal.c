/* reproduce_kernel_last_asid_refusal.c
 * Directed test of a precision failure in lib/kernel/k2_mmu_frames.c.
 * Sequence: user frame F; kernel space (ASID 0) maps F read-only, kernel-only;
 * user space 1 maps F read-only.
 * The only mapping of F is the kernel's, which no user space can reach, and neither
 * mapping is writable or executable. Native records the kernel's ASID as F's last
 * mapper and refuses the user mapping with PERM_ALIAS. A rule over the actual mappings
 * (no write/execute alias, no writable cross-ASID user sharing) would accept it.
 * Exit 0 when the refusal is reproduced exactly as described. */
#include <eshkol/kernel/k2_mmu_frames.h>
#include <stdio.h>
static void show(const char* step, k2_status_t st, const k2_frame_pool_t* p, uint32_t f) {
    const k2_frame_meta_t* m = &p->frames[f];
    printf("%-26s status %2d  refcount %u  union %u  last_asid %d\n", step, (int)st, m->map_refcount,
           m->mapped_perms & 7u, m->mapped_asid == K2_INVALID_INDEX ? -1 : (int)m->mapped_asid);
}
int main(void) {
    k2_frame_pool_t pool; k2_aspace_t kernel, user1; k2_page_frame_t f;
    if (k2_frame_pool_init(&pool, 0x200000ULL, 4, 0) || k2_aspace_init(&kernel, K2_MMU_X86_64_4L, 0, 0) ||
        k2_aspace_init(&user1, K2_MMU_X86_64_4L, 1, 1)) return 2;
    k2_status_t a = k2_frame_alloc_user(&pool, &f);
    show("alloc_user", a, &pool, f.frame_idx);
    k2_status_t k = k2_aspace_map(&kernel, &pool, 0x1000, &f, K2_PERM_READ | K2_PERM_KERNEL_ONLY);
    show("kernel map R|K", k, &pool, f.frame_idx);
    k2_status_t u = k2_aspace_map(&user1, &pool, 0x1000, &f, K2_PERM_READ | K2_PERM_USER);
    show("user1 map R|U", u, &pool, f.frame_idx);
    printf("expected: OK, OK, PERM_ALIAS (%d)\n", (int)K2_ERR_PERM_ALIAS);
    return (a == K2_OK && k == K2_OK && u == K2_ERR_PERM_ALIAS) ? 0 : 1;
}
