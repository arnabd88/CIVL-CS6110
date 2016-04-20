/* CppExpresLexerg: grammar for Cpp conditional expressions.
 * 
 *
 */
parser grammar PreprocessorExpressionParser;

options {
	language=Java;
	tokenVocab=PreprocessorLexer;
	output=AST;
}

tokens {
	EXPR; // root node
}

@header
{
package edu.udel.cis.vsl.abc.front.c.preproc;
}

// TODO: add bit-wise operators.  See Cpp manual.

start		:	expr EOF -> expr
		;

expr 		:	logical_or_expr
		;

/* 
 * logical or: e1 || e2 
 * Root: OR
 * child 0: e1
 * child 1: e2
 */
logical_or_expr	:	(logical_and_expr -> logical_and_expr)
			(OR arg=logical_and_expr -> ^(OR $logical_or_expr $arg))*
		;

/* 
 * logical and: e1 && e2 
 * Root: AND
 * child 0: e1
 * child 1: e2
 */
logical_and_expr:	(equality_expr -> equality_expr)
			(AND arg=equality_expr -> ^(AND $logical_and_expr $arg))*
		;

/* 
 * e1==e2  or  e1!=e2
 * Root: EQ or NEQ
 * child 0: e1
 * child 1: e2
 */
equality_expr	:	(relational_expr -> relational_expr)
			(op=equality_operator arg=relational_expr
			   -> ^($op $equality_expr $arg))*
		;

equality_operator
		:	EQUALS
		|	NEQ
		;

/* 
 * e1 > e2  e1 < e2  e1 >= e2  e1 <= e2
 * Root: one of LT, GT, LTE, GTE
 * child 0: e1
 * child 1: e2
 */
relational_expr	:	(additive_expr -> additive_expr)
			(op=relational_operator arg=additive_expr
			   -> ^($op $relational_expr $arg))*
		;

relational_operator
		:	LT
		|	GT
		|	LTE
		|	GTE
		;

/* e1+e2 or e1-e2
 * Root: PLUS or SUB
 * Child 0: e1
 * Child 1: e2
 */
additive_expr	:	(multi_expr -> multi_expr)
			(additive_operator arg=multi_expr
			   -> ^(additive_operator $additive_expr $arg))*
		;
additive_operator
		:	PLUS
		|	SUB
		;

/* e1*e2, e1/e2, or e1%e2
 * Root: MULTI, DIV, or MOD
 * Child 0: e1
 * Child 1: e2
 */	
multi_expr	:	(unary_expr -> unary_expr)
			(multi_operator unary_expr
			   -> ^(multi_operator $multi_expr unary_expr))*
		;

multi_operator	:	STAR
		|	DIV
		|	MOD
		;

/* Unary operators: +e, -e, !e, *e
 * Root: PLUS, SUB, NOT, MULTI
 * Child 0: e
 */
unary_expr	:	primary_expr
		|	unary_operator unary_expr -> ^(unary_operator unary_expr)
		;

unary_operator	:	PLUS
		|	SUB
		|	NOT
		|	STAR
		;	
		
primary_expr	:	pp_number
		|	LPAREN expr RPAREN -> expr
		|	DEFINED ( identifier | LPAREN identifier RPAREN )
			-> ^(DEFINED identifier)
		|	identifier
		;


white		:	WS | NEWLINE
		;

/* An "identifier" for the preprocessor is any C IDENTIFIER or C keyword: */

identifier	:	IDENTIFIER | c_keyword | civl_keyword | cuda_keyword | gnuc_keyword;

c_keyword	:	AUTO | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT
		| 	DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO
		|	IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN
		|	SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF
		|	UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF
		|	ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN
		|	STATICASSERT | THREADLOCAL
		;

civl_keyword	:	ASSIGNS | CHOOSE | COLLECTIVE
		| 	DEPENDS | ENSURES | FALSE | GUARD
		|	INPUT | INVARIANT | OUTPUT | PROC | READS
		|	REQUIRES | RESULT | SELF | PROCNULL | SPAWN | TRUE | HERE | ROOT 
		| 	WAIT | WHEN | FATOMIC | CALLS
		;

gnuc_keyword  :  TYPEOF;
		
cuda_keyword	:	DEVICE | GLOBAL | SHARED
		;


/* a "pp_number" is any PP_NUMBER, INTEGER_CONSTANT, or FLOATING_CONSTANT */
pp_number	:	INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER ;

