/*
  An instance of limits.h using minimal values.  See C11 5.2.4.2.1.
  There is also a choice involving the char type:

  "If the value of an object of type char is treated as a signed integer
  when used in an expression, the value of CHAR_MIN shall be the same as
  that of SCHAR_MIN and the value of CHAR_MAX shall be the same as that
  of SCHAR_MAX. Otherwise, the value of CHAR_MIN shall be 0 and the
  value of CHAR_MAX shall be the same as that of UCHAR_MAX.20) The value
  UCHAR_MAX shall equal 2CHAR_BIT − 1."

  This instance chooses to make char a signed integer type.
*/

#ifndef _LIMITS
#define _LIMITS

// number of bits for smallest object that is not a bit-field (byte)
#define CHAR_BIT 8

// minimum value for an object of type signed char
#define SCHAR_MIN -127 //−(2^7−1)

//maximum value for an object of type signed char
#define SCHAR_MAX +127 //2^7−1

// maximum value for an object of type unsigned char
#define UCHAR_MAX 255 //2^8−1

// minimum value for an object of type char
#define CHAR_MIN -127

//maximum value for an object of type char
#define CHAR_MAX +127

// maximum number of bytes in a multibyte character, for any supported locale
#define MB_LEN_MAX 1

// minimum value for an object of type short int
#define SHRT_MIN -32767 //−(2^15−1)

// maximum value for an object of type short int
#define SHRT_MAX +32767 //2^15−1

// maximum value for an object of type unsigned short int
#define USHRT_MAX 65535 //2^16−1

// minimum value for an object of type int
#define INT_MIN -32767 //−(2^15−1)

// maximum value for an object of type int
#define INT_MAX +32767 //2^15−1

// maximum value for an object of type unsigned int
#define UINT_MAX 65535 //2^16−1

// minimum value for an object of type long int
#define LONG_MIN -2147483647 //−(2^31−1)

// maximum value for an object of type long int
#define LONG_MAX +2147483647 //2^31−1

// maximum value for an object of type unsigned long int
#define ULONG_MAX 4294967295 //2^32−1

// minimum value for an object of type long long int
#define LLONG_MIN -9223372036854775807 //−(2^63−1)

// maximum value for an object of type long long int
#define LLONG_MAX +9223372036854775807 //2^63−1

// maximum value for an object of type unsigned long long int
#define ULLONG_MAX 18446744073709551615 //2^64−1
#endif
