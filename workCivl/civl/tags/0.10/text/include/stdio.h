/* stdio.h: The CIVL representation of standard C library stdio.
 * Based on C11 Standard.
 */
 #ifdef __STDIO__
 #else
 #define __STDIO__

/* Needed from stdarg.h: */

typedef struct _ABC_va_list {
  int x;
} va_list;

/* Types */

typedef unsigned long int size_t;

/* Represents an actual file: something with a name and contents.
 * The name is a string (array of char).  The contents is an
 * array of strings: each entry is a "chunk" of the file; the
 * file may be viewed as a concatenation of those chunks.
 */
typedef struct CIVL_file_t {
  char name[];        /* name of file */
  char contents[][];  /* list of strings which form file contents */
  _Bool isOutput;     /* is this an output file? */
  _Bool isInput;      /* is this an input file? */
  _Bool isBinary;     /* can be binary or text */
  _Bool isWide;       /* wide orientation */
} CIVL_file_t;

/* Implements the C notion of a FILE, which is really a reference
 * into a particular point of an actual file.  Even if you are just
 * reading the file, this FILE object changes since it contains a reference
 * to the point of file you just read.  
 *
 */
typedef struct FILE {
  CIVL_file_t *file;  // the actual file to which this refers 
  int pos1;     // the chunk index (first index) in the contents
  int pos2;     // the character index (second index) in the contents
  int mode;     // Stream mode: r/w/a 
  _Bool isOpen; // is this FILE open?
} FILE;

typedef int fpos_t;

/* Macros */

#define NULL ((void*)0)
#define _IOFBF 1
#define _IOLBF 2
#define _IONBF 3
#define BUFSIZ 100
#define EOF (-100)
#define FOPEN_MAX 100
#define FILENAME_MAX 500
#define L_tmpnam 500
#define SEEK_CUR 1
#define SEEK_END 2
#define SEEK_SET 3
#define TMP_MAX 100
#define stdin (FILE*)0
#define stdout (FILE*)1
#define stderr (FILE*)2

/* Global Variables */

// inputs: none, using abstract functions instead

// global state variables...

/* The files in the file system.  Initially empty array.
 * When a file is opened, a new actual file will be created
 * and added to this list, if a file by that name is not
 * already in this list.  The state of this array and
 * the files in this array change during execution.
 */
CIVL_file_t CIVL_files[];

// outputs:

/* The files which were modified or created are written here
 * at the end of the program.   They constitute outputs of
 * the program.  The files will be sorted in some canonical
 * way.
 */
$output CIVL_file_t CIVL_output_files[];

/* Function Prototypes */

#include<stdio-common.h>

#endif

