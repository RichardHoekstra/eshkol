/* reproduce_asid_collision.c
 * Directed test of a conditional isolation failure in lib/kernel/k2_mmu_frames.c.
 * Precondition violated on purpose: a kernel space and user space B share ASID 2.
 * Sequence: user frame F; user space A (ASID 1) maps F read-only; the kernel space maps
 * F read-only (F's recorded last ASID becomes 2); user space B (ASID 2) maps F writable.
 * Native accepts the last mapping, so A reads a frame B writes. With unique ASIDs the
 * last step is refused with PERM_ALIAS.
 * Exit 0 when the acceptance is reproduced and the unique-ASID control refuses. */
#include <eshkol/kernel/k2_mmu_frames.h>
#include <stdio.h>
static k2_status_t run(uint32_t kernel_asid, int verbose) {
    k2_frame_pool_t pool; k2_aspace_t kernel, a, b; k2_page_frame_t f;
    if (k2_frame_pool_init(&pool, 0x200000ULL, 4, 0) ||
        k2_aspace_init(&kernel, K2_MMU_X86_64_4L, kernel_asid, 0) ||
        k2_aspace_init(&a, K2_MMU_X86_64_4L, 1, 1) || k2_aspace_init(&b, K2_MMU_X86_64_4L, 2, 1) ||
        k2_frame_alloc_user(&pool, &f)) return (k2_status_t)-1;
    k2_status_t s1 = k2_aspace_map(&a, &pool, 0x2000, &f, K2_PERM_READ | K2_PERM_USER);
    k2_status_t s2 = k2_aspace_map(&kernel, &pool, 0x0000, &f, K2_PERM_READ | K2_PERM_KERNEL_ONLY);
    k2_status_t s3 = k2_aspace_map(&b, &pool, 0x5000, &f, K2_PERM_READ | K2_PERM_WRITE | K2_PERM_USER);
    if (verbose)
        printf("kernel ASID %u: A maps R|U -> %d; kernel maps R|K -> %d; B (ASID 2) maps R|W|U -> %d\n",
               kernel_asid, (int)s1, (int)s2, (int)s3);
    return (s1 == K2_OK && s2 == K2_OK) ? s3 : (k2_status_t)-1;
}
int main(void) {
    k2_status_t colliding = run(2, 1), unique = run(0, 1);
    printf("K2_OK = %d, K2_ERR_PERM_ALIAS = %d\n", (int)K2_OK, (int)K2_ERR_PERM_ALIAS);
    return (colliding == K2_OK && unique == K2_ERR_PERM_ALIAS) ? 0 : 1;
}
