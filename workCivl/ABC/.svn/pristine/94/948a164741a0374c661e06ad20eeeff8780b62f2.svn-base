parser grammar PreprocessorParser;

/* Author: Stephen F. Siegel, University of Delaware
 * Last modified: June 1, 2012
 *
 * Grammar for C preprocessor.
 * This grammar describes a C source file before preprocessing.
 * It does not execute any preprocessor directives.
 * It simply represents the file in a structured way.
 *
 * See the C11 Standard, Sec. 6.10.
 *
 * This grammar uses the PreprocessorLexer, which has already
 * formed the preprocessor tokens.
 *
 * CIVL-C keywords are also included and treated the same as C keywords.
 */

options {
   tokenVocab=PreprocessorLexer;
   output=AST;
}

/* "imaginary" tokens */
tokens {
	FILE;         // root node
	TEXT_BLOCK;   // a list of tokens
	PARAMLIST;    // x1,x2,x3
	EXPR;         // an expression used in a conditional (#if)
	SEQUENCE;     // true branch of conditional directive
	BODY;         // body of macro definition
}

@header
{
package edu.udel.cis.vsl.abc.front.c.preproc;
}

@members{
@Override
public void emitErrorMessage(String msg) { // don't try to recover!
    throw new RuntimeException(msg);
}
}

/**  The whole file consists of 1 block */
file		:	block -> ^(FILE block)
		;

/** A block is a sequence of directives and text blocks.
 *  A block may be empty.
 */
block		:	(directive | textblock)* ;

/** These are the various kind of preprocessor directives
 * specified in the C11 standard.   Each one whose name ends in
 * "block" is a complete block, so the "ifblock", for example,
 * contains everything up to and including the final "#endif".  
 *
 * Yes, a "nondirective" is a kind of directive.  That is what
 * C11 says.
 *
 */
directive	:	macrodef
		|	macroundef
		|	includeline
		|	pragmaline
		|	ifblock
		|	ifdefblock
		|	ifndefblock
		|	errorline
		|	lineline
		|	nondirectiveline
		;

/** A textblock is a maximal sequence of text lines.  A
 * text line is any line that doesn't have a "#' as its first
 * non-whitespace character.   In the tree, the text block
 * just contains a sequence of all the tokens form all the lines
 * concatenated.  The white space tokens and newlines are included,
 * as are comments. */
textblock	: 	(options {greedy=true;} : textline)+
			 -> ^(TEXT_BLOCK textline+) ;

textline	:	white* (nonPoundPpToken wpptoken*)? lineend ;

white		:	WS | COMMENT ;

wpptoken	:	pptoken | white ;

lineend		:	NEWLINE ;

macrodef	:	PDEFINE white+ i=identifier
			( paramlist macrobody -> ^(PDEFINE $i paramlist macrobody)
			| lineend -> ^(PDEFINE $i ^(BODY))
			| white macrobody -> ^(PDEFINE $i macrobody)
			)
		;

macrobody	:	white* 
			( t+=pptoken (t+=wpptoken* t+=pptoken)? white* lineend
			  -> ^(BODY $t+)
			| lineend
			  -> ^(BODY)
			)
		;

paramlist	:	LPAREN white* 
			( RPAREN -> ^(PARAMLIST)
			| identifier (white* COMMA white* identifier)* white* RPAREN
			  -> ^(PARAMLIST identifier+)
			)
		;

macroundef	:	PUNDEF white+ identifier white* lineend
			-> ^(PUNDEF identifier)
		;

includeline	:	PINCLUDE white* HEADER_NAME white* lineend
			-> ^(PINCLUDE HEADER_NAME)
		;

ifblock		: 	PIF white* expr	lineend block elseblock? endifline
			-> ^(PIF expr ^(SEQUENCE block?) elseblock?)		
		;

expr		:	ppdExpr (ppdExpr | white)* -> ^(EXPR ppdExpr+) ;

definedExpr	:	DEFINED WS!*
			( identifier
			| LPAREN! WS!* identifier WS!* RPAREN!
			)
		;
			
ppdExpr		:	pptoken | definedExpr ;

elseblock	:	simpleelseblock	| elifblock ;

simpleelseblock	:	PELSE white* lineend block -> ^(PELSE block?) ;

elifblock	:	c=PELIF white* expr lineend block elseblock? 
			->
			^($c ^($c expr ^(SEQUENCE block?) elseblock?))
		;

ifdefblock	:	PIFDEF white* identifier white* lineend
			block elseblock? endifline
			-> ^(PIFDEF identifier ^(SEQUENCE block?) elseblock?)
		;

ifndefblock	:	PIFNDEF white* identifier white* lineend
			block elseblock? endifline
			-> ^(PIFNDEF identifier ^(SEQUENCE block) elseblock?)
		;

endifline	:	PENDIF white* lineend ;

pragmaline	:	PRAGMA wpptoken* lineend -> ^(PRAGMA wpptoken* lineend)	;

errorline	:	PERROR wpptoken* lineend -> ^(PERROR wpptoken*)	;

lineline	:	PLINE wpptoken* lineend -> ^(PLINE wpptoken*) ;

nondirectiveline
		:	HASH wpptoken* lineend -> ^(HASH wpptoken*) ;

/* A "preprocessor token" as defined in the C11 Standard. */
pptoken		:	HEADER_NAME
		|	identifier
		|	pp_number
		|	CHARACTER_CONSTANT
		|	STRING_LITERAL
		|	punctuator
		|	OTHER
		;

/* Any preprocessor token other than '#' */
nonPoundPpToken	:	HEADER_NAME
		|	identifier
		|	pp_number
		|	CHARACTER_CONSTANT
		|	STRING_LITERAL
		|	nonPoundPunctuator
		|	OTHER
		;
		
/* An "identifier" for the preprocessor is any C IDENTIFIER or C keyword: */
/* Added for CIVL-C: any CIVL-C keyword */

identifier	:	IDENTIFIER | c_keyword | gnuc_keyword;

c_keyword	:	AUTO | ASSIGNS | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT
        |   DEPENDS | DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO
		|	GUARD | IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN
		|	SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF
		|	UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF
		|	ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN
		|	STATICASSERT | THREADLOCAL
        |   CHOOSE | COLLECTIVE
		|	ENSURES | FALSE | INPUT | INVARIANT
		|	OUTPUT | READS | REQUIRES | RESULT | SELF | PROCNULL | HERE | ROOT
		|	SPAWN | TRUE | WHEN | CIVLATOMIC | CIVLATOM
		|	ABSTRACT | BIG_O | CONTIN | DERIV | FORALL | EXISTS | UNIFORM | PURE 
		|	REAL | CIVLFOR | PARFOR | DOMAIN | RANGE | SYSTEM
		| 	DEVICE | GLOBAL | SHARED
        |   FATOMIC | CALLS
		;

gnuc_keyword : TYPEOF;

punctuator	:	nonPoundPunctuator | HASH ;

/* a "pp_number" is any PP_NUMBER, INTEGER_CONSTANT, or FLOATING_CONSTANT */
pp_number	:	INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER ;

/* Any punctuator other than '#' */
nonPoundPunctuator
		:	AMPERSAND
		|	AND
		|	ARROW
		|	ASSIGN
		|	AT
		|	BITANDEQ
		|	BITOR
		|	BITOREQ
		|	BITXOR
		|	BITXOREQ
		|	COLON
		|	COMMA
		|	DIV
		|	DIVEQ
		|	DOT
		|	DOTDOT
		|	ELLIPSIS
		|	EQUALS
		|	GT
		|	GTE
		|	HASHHASH
		|	IMPLIES
		|	LCURLY
		|	LEXCON
		|	LPAREN
		|	LSLIST
		|	LSQUARE
		|	LT
		|	LTE
		|	MINUSMINUS
		|	MOD
		|	MODEQ
		|	NEQ
		|	NOT
		|	OR
		|	PLUS
		|	PLUSEQ
		|	PLUSPLUS
		|	QMARK
		|	RCURLY
		|	REXCON
		|	RPAREN
		|	RSLIST
		|	RSQUARE
		|	SEMI
		|	SHIFTLEFT
		|	SHIFTLEFTEQ
		|	SHIFTRIGHT
		|	SHIFTRIGHTEQ
		|	STAR
		|	STAREQ
		|	SUB
		|	SUBEQ
		|	TILDE
		;
