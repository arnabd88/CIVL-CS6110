/* From C11 Sec. 6.7.2.1.19:
 *
 * EXAMPLE 1 The following illustrates anonymous structures and unions:
 * ...
 *  v1.i = 2;   // valid
 *  v1.k = 3;   // invalid: inner structure is not anonymous
 *  v1.w.k = 5; // valid
 */

struct v {
  union { // anonymous union
    struct { int i, j; }; // anonymous structure
    struct { long k, l;} w;
  };
  int m;
} v1;
