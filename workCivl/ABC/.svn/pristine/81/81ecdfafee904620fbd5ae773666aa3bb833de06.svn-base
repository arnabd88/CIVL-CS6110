lexer grammar PreprocessorLexer;

/*
 * Author: Stephen F. Siegel, University of Delaware
 * Last changed: June 2012
 *
 * This is a grammar for lexical analysis for a preprocessor
 * file.  It follows the C11 Standard.  This grammar assumes
 * that the stream of characters being scanned has already
 * gone through translation phases 1 and 2.  In particular
 * backslash followed by newline sequences have been removed.
 *
 * The grammar has been extended to include keywords for
 * the CIVL-C extension of C.
 */

@header
{
package edu.udel.cis.vsl.abc.front.c.preproc;
}

@members
{

public boolean inInclude = false; // are we inside a #include directive?
public boolean inCondition = false; // are we inside a #if condition?
public boolean atLineStart = true; // are we at start of line + possible WS?

@Override
public void emitErrorMessage(String msg) { // don't try to recover!
    throw new RuntimeException(msg);
}

}


/* Preprocessor directives and pragmas */

fragment
NotLineStart	:	{atLineStart = false;} ;

PDEFINE		:	{atLineStart}?=>WS* '#' WS* 'define' NotLineStart;
PINCLUDE	:	{atLineStart}?=>WS* '#' WS* 'include'
			{inInclude = true; atLineStart=false;}
		;
PIFDEF		:	{atLineStart}?=>WS* '#' WS* 'ifdef' NotLineStart;
PIFNDEF		:	{atLineStart}?=>WS* '#' WS* 'ifndef' NotLineStart;
PIF		:	{atLineStart}?=>WS* '#' WS* 'if'
			{inCondition = true; atLineStart = false;}
		;
PENDIF		:	{atLineStart}?=>WS* '#' WS* 'endif' NotLineStart;
PELIF		:	{atLineStart}?=>WS* '#' WS* 'elif'
			{inCondition = true; atLineStart = false;}
		;
PELSE		:	{atLineStart}?=>WS* '#' WS* 'else' NotLineStart;
PRAGMA		:	{atLineStart}?=>WS* '#' WS* 'pragma' NotLineStart;
PERROR		:	{atLineStart}?=>WS* '#' WS* 'error' NotLineStart;
PUNDEF		:	{atLineStart}?=>WS* '#' WS* 'undef' NotLineStart;
PLINE		:	{atLineStart}?=>WS* '#' WS* 'line' NotLineStart;
//PBLANK		:	{atLineStart}?=>WS* '#' WS* NotLineStart;
HASH		:	WS* '#' WS*;
DEFINED		:	{inCondition}?=>'defined' NotLineStart;

/****** White space ******/

NEWLINE		:	NewLine;

fragment
NewLine		:	'\r'? '\n'
			{inCondition=false; atLineStart=true;};

WS		:	(' ' | '\t')+;


/****** C keywords, from C11 Sec. 6.4.1 ******/

// These are listed in the order in which they are listed
// in the C11 Standard.
// Do NOT put CIVL-C keywords here.  They go below!

AUTO		:	'auto';
BREAK		:	'break';
CASE		:	'case';
CHAR		:	'char';
CONST		:	'const';
CONTINUE	:	'continue';
DEFAULT		:	'default';
DO			:	'do';
DOUBLE		:	'double';
ELSE		:	'else';
ENUM		:	'enum';
EXTERN		:	'extern';
FLOAT		:	'float';
FOR			:	'for';
GOTO		:	'goto';
IF			:	'if';
INLINE		:	'inline';
INT			:	'int';
LONG		:	'long';
REGISTER	:	'register';
RESTRICT	:	'restrict';
RETURN		:	'return';
SHORT		:	'short';
SIGNED		:	'signed';
SIZEOF		:	'sizeof';
STATIC		:	'static';
STRUCT		:	'struct';
SWITCH		:	'switch';
TYPEDEF		:	'typedef';
UNION		:	'union';
UNSIGNED	:	'unsigned';
VOID		:	'void';
VOLATILE	:	'volatile';
WHILE		:	'while';
ALIGNAS		:	'_Alignas';
ALIGNOF		:	'_Alignof';
ATOMIC		:	'_Atomic';
BOOL		:	'_Bool';
COMPLEX		:	'_Complex';
GENERIC		:	'_Generic';
IMAGINARY	:	'_Imaginary';
NORETURN	:	'_Noreturn';
STATICASSERT:	'_Static_assert';
THREADLOCAL	:	'_Thread_local';


/* Additional keywords and symbols used in CIVL-C */

// Keep these in alphabetical order by token name.  Respect the formatting!
// Be sure to add these to PreprocessorParser.g too, under c_keyword.

ABSTRACT	:	'$abstract';
ASSIGNS     :   '$assigns';
AT			:	'@';
BIG_O		:	'$O';
CALLS       :   '$calls';
CHOOSE		:	'$choose';
CIVLATOMIC	:	'$atomic';
CIVLATOM	:	'$atom';
CIVLFOR		:	'$for';
COLLECTIVE	:	'$collective';
CONTIN		:	'$contin';
DEPENDS     :   '$depends';
DERIV		:	'$D';
DOMAIN		:	'$domain';
ENSURES		:	'$ensures';
EXISTS		: 	'$exists';
FALSE		:	'$false';
FORALL		:	'$forall';
FATOMIC     :   '$atomic_f';
GUARD       :   '$guard';
HERE		:	'$here';
IMPLIES		:	'=>'	|	NotLineStart; // can the NotLineStart be removed?
INPUT		:	'$input';
INVARIANT	:	'$invariant';
LSLIST		:	'<|';  // LSLIST and RSLIST enclose a scope list
OUTPUT		:	'$output';
PARFOR		:	'$parfor';
PROCNULL	:	'$proc_null';
PURE        :   '$pure';
RANGE		:	'$range';
REAL		:	'$real';
REQUIRES	:	'$requires';
RESULT		:	'$result';
RSLIST		:	'|>';  // LSLIST and RSLIST enclose a scope list
SCOPEOF		:	'$scopeof';
SELF		:	'$self';
READS       :   '$reads';
SPAWN		:	'$spawn';
SYSTEM      :   '$system';
TRUE		:	'$true';
UNIFORM		:	'$uniform';
WHEN		:	'$when';

/* Cuda-C keywords */

DEVICE  :   '__device__';
GLOBAL	:	'__global__';
SHARED	:	'__shared__';

/* GNU C keywords */
TYPEOF  :   'typeof';

/****** Identifiers: C11 Sec. 6.4.2 ******/

IDENTIFIER	:	IdentifierNonDigit
			(IdentifierNonDigit | Digit)* NotLineStart
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
NonDigit	:	'A'..'Z' | 'a'..'z' | '_' | '$';

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
OctalConstant	:	Zero OctalDigit* IntegerSuffix? NotLineStart;

fragment
HexadecimalConstant
		:	HexPrefix HexadecimalDigit+ IntegerSuffix? NotLineStart;

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
			NotLineStart
		;


/****** Sec. 6.4.4.4: Character Constants ******/

CHARACTER_CONSTANT
		:	('L' | 'U' | 'u')? '\'' CChar+ '\'' NotLineStart;

fragment
CChar		:	~('\'' | '\\' | '\n') | EscapeSequence ;

fragment
EscapeSequence	:	'\\' ( '\'' | '"' | '\?' | '\\' |
			       'a' | 'b' | 'f' | 'n' |'r' | 't' | 'v'
			     )
		|	OctalEscape
		|	HexEscape
		;
fragment
OctalEscape	:	'\\' OctalDigit (OctalDigit OctalDigit?)? ;

fragment
OctalDigit	:	'0' .. '7';

fragment
HexEscape	:	'\\' 'x' HexadecimalDigit+ ;


/****** 6.4.5: String Literals *****/


STRING_LITERAL  :	('u8' | 'u' | 'U' | 'L')? '"' SChar* '"'
			NotLineStart
		;

fragment
SChar		:	~('"' | '\\' | '\n') | EscapeSequence ;


/****** Punctuators: C11 Sec. 6.4.6 ******/

ELLIPSIS	: '...' NotLineStart;
DOTDOT		: '..' NotLineStart;
DOT			:	'.' NotLineStart;
AMPERSAND	:	'&'		NotLineStart;
AND		:	'&&'		NotLineStart;
ARROW		:	'->'		NotLineStart;
ASSIGN		:	'='		NotLineStart;
BITANDEQ	:	'&='		NotLineStart;
BITOR		:	'|'		NotLineStart;
BITOREQ		:	'|='		NotLineStart;
BITXOR		:	'^'		NotLineStart;
BITXOREQ	:	'^='		NotLineStart;
COLON		:	':'		NotLineStart;
COMMA		:	','		NotLineStart;
DIV		:	'/'		NotLineStart;
DIVEQ		:	'/='		NotLineStart;
EQUALS		:	'=='		NotLineStart;
GT		:	'>'		NotLineStart;
GTE		:	'>='		NotLineStart;
//HASH		:	'#' | '%:'	NotLineStart;
HASHHASH	:	'##' | '%:%:'	NotLineStart;
LCURLY		:	'{' | '<%'	NotLineStart;
LEXCON		:	'<<<' NotLineStart;
LPAREN		:	'('		NotLineStart;
LSQUARE		:	'[' | '<:'	NotLineStart;
LT		:	'<'		NotLineStart;
LTE		:	'<='		NotLineStart;
MINUSMINUS	:	'--'		NotLineStart;
MOD		:	'%'		NotLineStart;
MODEQ		:	'%='		NotLineStart;
NEQ		:	'!='		NotLineStart;
NOT		:	'!'		NotLineStart;
OR		:	'||'		NotLineStart;
PLUS		:	'+'		NotLineStart;
PLUSEQ		:	'+='		NotLineStart;
PLUSPLUS	:	'++'		NotLineStart;
QMARK		:	'?'		NotLineStart;
RCURLY		:	'}' | '%>'	NotLineStart;
REXCON		:	'>>>' NotLineStart;
RPAREN		:	')'		NotLineStart;
RSQUARE		:	']' | ':>'	NotLineStart;
SEMI		:	';'		NotLineStart;
SHIFTLEFT	:	'<<'		NotLineStart;
SHIFTLEFTEQ	:	'<<='		NotLineStart;
SHIFTRIGHT	:	'>>'		NotLineStart;
SHIFTRIGHTEQ	:	'>>='		NotLineStart;
STAR		:	'*'		NotLineStart;
STAREQ		:	'*='		NotLineStart;
SUB		:	'-'		NotLineStart;
SUBEQ		:	'-='		NotLineStart;
TILDE		:	'~'		NotLineStart;

/****** Header Names: C11 Sec. 6.4.7 ******/
	
HEADER_NAME	:	{inInclude}?=>
			( '"' (~('\n' | '"'))+ '"'
			| '<' (~('\n' | '>'))+ '>'
			)
			{inInclude=false; atLineStart=false;}
		;
		

/* ***** Comments: C11 Sec 6.4.9 ******/

COMMENT		:	'//' ( options {greedy=true;} : ~('\n'|'\r') )*
		|	'/*' ( options {greedy=false;} : . )* '*/'
		;
		
/****** Other characters: C11 Sec. 6.4 ******/

OTHER		:	. NotLineStart;
