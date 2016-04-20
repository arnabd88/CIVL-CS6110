lexer grammar AcslLexer;

/*
 * Author: Manchun Zheng, University of Delaware
 * Last changed: June 2012
 *
 * This is a grammar for lexical analysis for ACSL.  
 * It follows the ACSL 1.9 Standard.
 *
 * The grammar has been extended to include keywords for
 * the CIVL-C extension of ACSL.
 */

@header
{
package edu.udel.cis.vsl.abc.front.c.preproc;
}

/* types */
BOOLEAN :   'boolean';
INTEGER :   'integer';
REAL    :   'real';

CHAR		:	'char';
DOUBLE		:	'double';
FLOAT		:	'float';
INT			:	'int';
LONG		:	'long';
SHORT		:	'short';
VOID		:	'void';

/* keywords of clauses */
REQUIRES:   'requires';
TERMINATES: 'terminates';
DECREASES:  'decreases';
GUARDS  :   'guards';
ASSIGNS :   'assigns';
ENSURES :   'ensures';
ALLOC   :   'allocates';
BEHAVIORS:   'behaviors';
BEHAVIOR:   'behavior';
ASSUMES :   'assumes';
COMPLETE:   'complete';
DISJOINT:   'disjoint';
LOOP    :   'loop';
VARIANT :   'variant';
INVARIANT:  'invariant';
FREES   :   'frees';
//CIVL extensions
DEPENDS :   'depends';
READS   :   'reads';
PURE    :   'pure';

//CIVL-C constants
SELF    :   '$self';
//CIVL-MPI extensions
//---constants:
MPI_COMM_SIZE : '\\mpi_comm_size';
MPI_COMM_RANK : '\\mpi_comm_rank';
COL : 'COL';
P2P : 'P2P';
BOTH : 'BOTH';
//---constructors:
MPI_COLLECTIVE : '\\mpi_collective';
//---expressions:
MPI_EMPTY_IN : '\\mpi_empty_in';
MPI_EMPTY_OUT : '\\mpi_empty_out';
MPI_AGREE : '\\mpi_agree';
MPI_REGION : '\\mpi_region';
MPI_EQUALS : '\\mpi_equals';
REMOTE_ACCESS : '\\remote' ;

/* keywords of terms */
EMPTY   :   '\\empty';
OLD     :   '\\old';
RESULT  :   '\\result';
NOTHING :   '\\nothing';
UNION   :   '\\union';
INTER   :   '\\inter';
TRUE    :   '\\true';
FALSE   :   '\\false';
WITH    :   '\\with';
LET     :   '\\let';
SIZEOF  :   'sizeof';
FOR     :   'for';
READ    :   '\\read';
WRITE   :   '\\write';
REACH :   '\\reach';
CALL    :   '\\call';
NOACT   :   '\\noact';
ANYACT  :   '\\anyact';
FORALL  :   '\\forall';
EXISTS  :   '\\exists';
VALID   :   '\\valid';
NULL    :   '\\null';

/* operators */
PLUS    :   '+';
SUB   :   '-';
STAR    :   '*';
DIVIDE  :   '/';
MOD     :   '%';
SHIFTLEFT  :   '<<';
SHIFTRIGHT  :   '>>';
EQ      :   '==';
NEQ     :   '!=';
LTE     :   '<=';
GTE     :   '>=';
LT      :   '<';
GT      :   '>';
LAND    :   '&&';
LOR     :   '||';
BAR     :   '|';
XOR     :   '^^';
AMPERSAND    :   '&';
IMPLY   :   '==>';
EQUIV   :   '<==>';
ARROW   :   '->';
BITXOR  :   '^';
NOT     :   '!';
COMP    :   '~';
ELLIPSIS:   '...';
DOTDOT  :   '..';
DOT     :   '.';
QUESTION:   '?';
COLON   :   ':';
SEMICOL :   ';';
COMMA   :   ',';
LPAREN  :   '(';
RPAREN  :   ')';
LCURLY  :   '{';
RCURLY  :   '}';
LSQUARE :   '[';
RSQUARE :   ']';
ASSIGN  :   '=';
HASH    :   '#';

/****** Sec. 6.4.4.1: Integer constants ******/

INTEGER_CONSTANT
		:	DecimalConstant IntegerSuffix?
		|	OctalConstant IntegerSuffix?
		|	HexadecimalConstant IntegerSuffix?
		;

fragment
DecimalConstant	:	NonZeroDigit Digit* ;


fragment
IntegerSuffix	:	UnsignedSuffix LongSuffix?
		|	UnsignedSuffix LongLongSuffix
		|	LongSuffix UnsignedSuffix?
		|	LongLongSuffix UnsignedSuffix?
		;

fragment
UnsignedSuffix	:	'u' | 'U';

fragment
LongSuffix	:	'l' | 'L';

fragment
LongLongSuffix	:	'll' | 'LL';

fragment	
OctalConstant	:	Zero OctalDigit* IntegerSuffix?;

fragment
HexadecimalConstant
		:	HexPrefix HexadecimalDigit+ IntegerSuffix?;

fragment
HexPrefix	:	Zero ('x' | 'X') ;

/****** Sec. 6.4.4.2: Floating Constants ******/

FLOATING_CONSTANT
		:	DecimalFloatingConstant
		|	HexadecimalFloatingConstant
		;

fragment
DecimalFloatingConstant
		:	FractionalConstant ExponentPart? FloatingSuffix?
		|	Digit+ ExponentPart FloatingSuffix?
		;

fragment
FractionalConstant
		:	Digit* DOT Digit+
		|	Digit+ DOT
		;

fragment
ExponentPart	:	('e' | 'E') ('+' | '-')? Digit+ ;

fragment
FloatingSuffix	:	'f' | 'l' | 'F' | 'L' ;

fragment
HexadecimalFloatingConstant
		:	HexPrefix HexFractionalConstant BinaryExponentPart
			FloatingSuffix?
		|	HexPrefix HexadecimalDigit+ BinaryExponentPart
			FloatingSuffix?
		;

fragment
HexFractionalConstant
		:	HexadecimalDigit* DOT HexadecimalDigit+
		|	HexadecimalDigit+ DOT 
		;

fragment
BinaryExponentPart
		:	('p' | 'P') ('+' | '-')? Digit+ ;


/****** Preprocessing Numbers: C11 Sec 6.4.8 ******/

/* PP_NUMBER should be anything that doesn't match the previous
 * rules but does match this one.
 */
PP_NUMBER	:	'.'? Digit
			( '.'
			| IdentifierNonDigit
			| Digit
			| ('e' | 'E' | 'p' | 'P') ('+' | '-')
			)*
		
		;


/****** 6.4.5: String Literals *****/


STRING_LITERAL  :	('u8' | 'u' | 'U' | 'L')? '"' SChar* '"'
		;

fragment
SChar		:	~('"' | '\\' | '\n') | EscapeSequence ;


fragment
EscapeSequence	:	'\\' ( '\'' | '"' | '\?' | '\\' |
			       'a' | 'b' | 'f' | 'n' |'r' | 't' | 'v'
			     )
		|	OctalEscape
		;
fragment
OctalEscape	:	'\\' OctalDigit (OctalDigit OctalDigit?)? ;

fragment
OctalDigit	:	'0' .. '7';

//import PreprocessorLexer;

ID	    :	IdentifierNonDigit
			(IdentifierNonDigit | Digit)*
		;
		
fragment
IdentifierNonDigit
		:	NonDigit | UniversalCharacterName ;

fragment
Zero		:	'0' ;

fragment
Digit		:	Zero | NonZeroDigit ;

fragment
NonZeroDigit	:	'1' .. '9' ;

fragment
NonDigit	:	'A'..'Z' | 'a'..'z' | '_' | '\\' | '$';

fragment
UniversalCharacterName
		:	'\\' 'u' HexQuad 
		|	'\\' 'U' HexQuad HexQuad
		;

fragment
HexQuad		:	HexadecimalDigit HexadecimalDigit HexadecimalDigit HexadecimalDigit ;

fragment
HexadecimalDigit
		:	'0'..'9' | 'a'..'f' | 'A'..'F' ;

/* Comment */

LCOMMENT
    :   '/*';

RCOMMENT
    :   '*/';

/* AT */
AT
    : '@'{$channel=HIDDEN;}
    ;

/*  */
NEWLINE		:	NewLine {$channel=HIDDEN;};

fragment
NewLine		:	'\r'? '\n';

WS		:	(' '{$channel=HIDDEN;} | '\t'{$channel=HIDDEN;})+;

