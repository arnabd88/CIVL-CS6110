/* CIVL model of string.h */

#ifdef __CIVLC__
#else
#include<civlc.h>
#endif
#include<string-common.h>

/* Copies a region of memory */
void memcpy(void *p, void *q, size_t size) {
  $atom {
    $bundle bundle = $bundle_pack(q, size);
    $bundle_unpack(bundle, p);
  }
}
