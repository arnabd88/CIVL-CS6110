/* CIVL model of string.h */

#ifdef __STRING__
#else
#define __STRING__
#include<string-common.h>
#include<civlc.h>

/* Copies a region of memory */
void* memcpy(void *p, void *q, const size_t size) {
  $atom {
    $bundle bundle = $bundle_pack(q, size);
    $bundle_unpack(bundle, p);
  }
  return p;
}

#endif
