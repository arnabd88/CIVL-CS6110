/* ABC model of string.h */

#ifndef __STRING__
#define __STRING__

#include <stddef.h>

/* copies n characters from the object pointed to by s2 into the 
   object pointed to by s1. If copying takes place between objects that overlap, 
   the behavior is undefined. */
void* memcpy (void *p, const void *q, size_t size);

/* Copy n bytes of src to dest, guaranteeing
   correct behavior for overlapping strings.  */
void* memmove (void *dest, const void *src, size_t n);

/* copies the value of c into each of the first 
   characters of the object pointed to by s */
$system void * memset(void *s, int c, size_t n);

/* Compare N bytes of S1 and S2.  */
int memcmp(const void *s1, const void *s2, size_t n);

/* Search N bytes of S for C.  */
void* memchr (const void * s, int c, size_t n);

/* copies the string pointed to by s2 (including the terminating null character) 
   into the array pointed to by s1. If copying takes place between objects that 
   overlap, the behavior is undefined. */
$system char *strcpy(char * restrict s1, const char * restrict s2);

/* Copy no more than N characters of SRC to DEST.  */
char *strncpy(char *dest, const char *src, size_t n);

/* Append SRC onto DEST.  */
char *strcat (char *dest, const char *src);

/* Append no more than N characters from SRC onto DEST.  */
char *strncat (char *dest, const char *src, size_t n);

/* Compare S1 and S2 */
$system int strcmp(const char *s1, const char *s2);

/* Compare N characters of S1 and S2 */
int strncmp(const char *s1, const char *s2, size_t n);

/* Compare the collated forms of S1 and S2 */
int strcoll(const char *s1, const char *s2);

/* Put a transformation of SRC into no more than N bytes of DEST. */
size_t strxfrm(char *dest, const char *src, size_t n);

/* Find the first occurrence of C in S.  */
char *strchr (const char * s, int c);

/* Find the last occurrence of C in S.  */
char *strrchr (const char * s, int c);

/* Return the length of the initial segment of S which
   consists entirely of characters not in REJECT.  */
size_t strcspn(const char *s, const char *reject);

/* Return the length of the initial segment of S which
   consists entirely of characters in ACCEPT.  */
size_t strspn (const char *s, const char *accept);

/* Find the first occurrence in S of any character in ACCEPT.  */
char *strpbrk (const char *s, const char *accept);

/* Find the first occurrence of S2 in S1.  */
char * strstr (const char *s1, const char *s2);

/* Divide S into tokens separated by characters in DELIM.  */
char * strtok (char *s, const char *delim);

/* computes the length of the string pointed to by s. */
$system size_t strlen(const char *s);

/* Return a string describing the meaning of the `errno' code in ERRNUM.  */
char * strerror(int errnum);

#endif
