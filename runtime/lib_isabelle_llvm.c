/*
 * Isabelle LLVM support library
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void isabelle_llvm_abort() {
  printf("%s\n","Isabelle-LLVM (abort): Dynamic check failed.");
  abort();
}

void isabelle_llvm_abort_msg(char const *msg) {
  printf("Isabelle-LLVM (abort): %s\n",msg);
  abort();
}

/* Allocation for the exported code. isabelle_llvm_calloc / isabelle_llvm_free keep exact-size
 * free lists for blocks of 1..256 bytes, at most 4096 blocks per size. Every block carries a 16-byte
 * header recording its size, so free() can classify it; the returned pointer is still n*m
 * zero-filled bytes, as calloc's contract requires. Not thread-safe: there are no locks. */
#define HDR_SIZE 16u   /* keeps the returned user pointer 16-byte aligned */

#define BUCKET_MIN 1u        /* size 0 is not bucketed */
#define BUCKET_MAX 256u      /* largest bucketed size */
#define BUCKET_CAP 4096u     /* max blocks retained per size */

static void *bucket_free[BUCKET_MAX + 1];
static unsigned bucket_len[BUCKET_MAX + 1];

static void **bucket_for(size_t total) {
  if (total >= BUCKET_MIN && total <= BUCKET_MAX) return &bucket_free[total];
  return NULL;
}

char* isabelle_llvm_calloc(size_t n, size_t m) {
  /* calloc's n*m overflow check, which the header-prefixed allocation would otherwise lose */
  size_t total;
  if (__builtin_mul_overflow(n, m, &total)) isabelle_llvm_abort_msg("Out of memory");
  void **slot = bucket_for(total);
  if (slot && *slot) {
    char *raw = (char*)(*slot);
    *slot = *(void **)raw;               /* pop: `next` was stashed in the header slot */
    bucket_len[total]--;
    char *user = raw + HDR_SIZE;
    memset(user, 0, total);
    *(size_t *)raw = total;
    return user;
  }
  char *raw = (char*)(calloc(1, HDR_SIZE + total));
  if (!raw) isabelle_llvm_abort_msg("Out of memory");
  *(size_t *)raw = total;
  return raw + HDR_SIZE;
}

void isabelle_llvm_free(char *p) {
  if (!p) return;
  char *raw = p - HDR_SIZE;
  size_t total = *(size_t *)raw;
  void **slot = bucket_for(total);
  if (slot && bucket_len[total] < BUCKET_CAP) {
    *(void **)raw = *slot;               /* push: the size is no longer needed once the
                                             bucket is known -- reuse the header slot for `next` */
    *slot = raw;
    bucket_len[total]++;
  } else {
    free(raw);
  }
}

