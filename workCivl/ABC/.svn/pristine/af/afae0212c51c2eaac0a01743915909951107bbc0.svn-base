/* Grammar for programming CIVL-C.
 * Based on C11 grammar.
 *
 * Author: Stephen F. Siegel, University of Delaware
 *
 * This grammar assumes the input token stream is the result of
 * translation phase 7, as specified in the C11 Standard.
 * In particular, all the preprocessing has already been
 * done.  
 *
 * In addition to the Standard, I borrowed from the older
 * C grammar included with the ANTLR distribution.
 *
 */
parser grammar CivlCParser;

options
{
	language=Java;
	tokenVocab=PreprocessorParser;
	output=AST;
}

tokens
{
	ABSENT;                   // represents missing syntactic element
	ABSTRACT_DECLARATOR;      // declarator without identifier
	ARGUMENT_LIST;            // list of arguments to an operator
	ARRAY_ELEMENT_DESIGNATOR; // [idx]=expr
	ARRAY_SUFFIX;             // [..] used in declarator
	BLOCK_ITEM_LIST;          // list of block items
	CALL;                     // function call
	CASE_LABELED_STATEMENT;   // case CONST: stmt
	CAST;                     // type cast operator
	COMPOUND_LITERAL;         // literal for structs, etc.
	COMPOUND_STATEMENT;       // { ... }
	CONTRACT;                 // procedure contracts
	DECLARATION;              // a declaration
	DECLARATION_LIST;         // list of declarations
	DECLARATION_SPECIFIERS;   // list of declaration specifiers
	DECLARATOR;               // a declarator
	DEFAULT_LABELED_STATEMENT;// default: stmt
	DERIVATIVE_EXPRESSION;    // complete derivative expression
	DESIGNATED_INITIALIZER;   // used in compound initializer
	DESIGNATION;              // designation, used in compound initializer
	DIRECT_ABSTRACT_DECLARATOR;   // direct declarator sans identifier
	DIRECT_DECLARATOR;        // declarator after removing leading *s
	ENUMERATION_CONSTANT;     // use of enumeration constant
	ENUMERATOR;               // identifier and optional int constant
	ENUMERATOR_LIST;          // list of enumerators in enum type definition
	EXPR;                     // symbol indicating "expression"
	EXPRESSION_STATEMENT;     // expr; (expression used as stmt)
	FIELD_DESIGNATOR;         // .id=expr
	FUNCTION_DEFINITION;      // function definition (contains body)
	FUNCTION_SUFFIX;          // (..) used in declarator
	GENERIC_ASSOCIATION;      // a generic association
	GENERIC_ASSOC_LIST;       // generic association list
	IDENTIFIER_LABELED_STATEMENT; // label: stmt
	IDENTIFIER_LIST;          // list of parameter names only in function decl
	INDEX;                    // array subscript operator
	INITIALIZER_LIST;         // initializer list in compound initializer
	INIT_DECLARATOR;          // initializer-declaration pair
	INIT_DECLARATOR_LIST;     // list of initializer-declarator pairs
	OPERATOR;                 // symbol indicating an operator
	PARAMETER_DECLARATION;    // parameter declaration in function decl
	PARAMETER_LIST;           // list of parameter decls in function decl
	PARAMETER_TYPE_LIST;      // parameter list and optional "..."
	PARENTHESIZED_EXPRESSION; // ( expr )
	PARTIAL;                  // CIVL-C partial derivative operator
	PARTIAL_LIST;             // list of partial operators
	POINTER;                  // * used in declarator
	POST_DECREMENT;           // expr--
	POST_INCREMENT;           // expr++
	PRE_DECREMENT;            // --expr
	PRE_INCREMENT;            // ++expr
	PROGRAM;                  // whole program (linking translation units)
	SCALAR_INITIALIZER;       // initializer for scalar variable
	SPECIFIER_QUALIFIER_LIST; // list of type specifiers and qualifiers
    STATEMENT;                // a statement
    STATEMENT_EXPRESSION;     // a statement expression (GNU C extension)
	STRUCT_DECLARATION;       // a field declaration
	STRUCT_DECLARATION_LIST;  // list of field declarations
	STRUCT_DECLARATOR;        // a struct/union declarator
	STRUCT_DECLARATOR_LIST;   // list of struct/union declarators
	TOKEN_LIST;               // list of tokens, e.g., in pragma
	TRANSLATION_UNIT;         // final result of translation
	TYPE;                     // symbol indicating "type"
	TYPEDEF_NAME;             // use of typedef name
    TYPEOF_EXPRESSION;
    TYPEOF_TYPE;
	TYPE_NAME;                // type specification without identifier
	TYPE_QUALIFIER_LIST;      // list of type qualifiers
}

scope Symbols {
    Set<String> types; // to keep track of typedefs
    Set<String> enumerationConstants; // to keep track of enum constants
    boolean isFunctionDefinition; // "function scope": entire function definition
}

scope DeclarationScope {
    boolean isTypedef; // is the current declaration a typedef
    boolean typedefNameUsed;
}

@header
{
package edu.udel.cis.vsl.abc.front.c.parse;

import java.util.Set;
import java.util.HashSet;
import edu.udel.cis.vsl.abc.front.IF.RuntimeParseException;
}

@members {
	public void setSymbols_stack(Stack<ScopeSymbols> symbols){
		this.Symbols_stack = new Stack();
		while(!symbols.isEmpty()){
			ScopeSymbols current = symbols.pop();
			Symbols_scope mySymbols = new Symbols_scope();

			mySymbols.types = current.types;
			mySymbols.enumerationConstants = current.enumerationConstants;
			Symbols_stack.add(mySymbols);
		}
	}

	@Override
	public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
		String hdr = getErrorHeader(e);
		String msg = getErrorMessage(e, tokenNames);
		
		throw new RuntimeParseException(hdr+" "+msg, e.token);
	}

	@Override
	public void emitErrorMessage(String msg) { // don't try to recover!
	    throw new RuntimeParseException(msg);
	}

	boolean isTypeName(String name) {
		for (Object scope : Symbols_stack)
			if (((Symbols_scope)scope).types.contains(name)) return true;
		return false;
	}

	boolean isEnumerationConstant(String name) {
		boolean answer = false;
		
		// System.err.print("Is "+name+" an enumeration constant: ");
		for (Object scope : Symbols_stack) {
			if (((Symbols_scope)scope).enumerationConstants.contains(name)) {
				answer=true;
				break;
			}
		}
		// System.err.println(answer);
		// System.err.flush();
		return answer;
	}	
}

/* ***** A.2.1: Expressions ***** */

/* Constants from A.1.5 */

constant
	: enumerationConstant
	| INTEGER_CONSTANT
	| FLOATING_CONSTANT
	| CHARACTER_CONSTANT
	| SELF | PROCNULL | TRUE | FALSE | RESULT
	| HERE | ROOT | ELLIPSIS
	;

enumerationConstant
	: {isEnumerationConstant(input.LT(1).getText())}? IDENTIFIER ->
	  ^(ENUMERATION_CONSTANT IDENTIFIER)
	;

/* 6.5.1 */
primaryExpression
	: constant
	| IDENTIFIER
	| STRING_LITERAL
    | LPAREN compoundStatement RPAREN
      -> ^(STATEMENT_EXPRESSION LPAREN compoundStatement RPAREN)
	| LPAREN expression RPAREN 
	  -> ^(PARENTHESIZED_EXPRESSION LPAREN expression RPAREN)
	| genericSelection
	| derivativeExpression
	;

/* 6.5.1.1 */
genericSelection
	: GENERIC LPAREN assignmentExpression COMMA genericAssocList
	  RPAREN
	  -> ^(GENERIC assignmentExpression genericAssocList)
	;

/* A CIVL-C derivative expression.  Some sequence
 * of partial-differentiation operators applied to a function.
 */
derivativeExpression
	: DERIV LSQUARE IDENTIFIER COMMA partialList RSQUARE 
	  LPAREN argumentExpressionList RPAREN
	  -> ^(DERIVATIVE_EXPRESSION IDENTIFIER partialList
	       argumentExpressionList RPAREN)
	;

/* A list of partial derivative operators.
 */
partialList
	: partial (COMMA partial)* -> ^(PARTIAL_LIST partial+)
	;

/* A partial-derivative operator */
partial
	: LCURLY IDENTIFIER COMMA INTEGER_CONSTANT RCURLY 
	  -> ^(PARTIAL IDENTIFIER INTEGER_CONSTANT)
	;

/* 6.5.1.1 */
genericAssocList
	: genericAssociation (COMMA genericAssociation)*
	  -> ^(GENERIC_ASSOC_LIST genericAssociation+)
	;

/* 6.5.1.1 */
genericAssociation
	: typeName COLON assignmentExpression
	  -> ^(GENERIC_ASSOCIATION typeName assignmentExpression)
	| DEFAULT COLON assignmentExpression
	  -> ^(GENERIC_ASSOCIATION DEFAULT assignmentExpression)
	;

/* 6.5.2 */
postfixExpression
	: (postfixExpressionRoot -> postfixExpressionRoot)
		// array index operator:
	  ( l=LSQUARE expression RSQUARE
	    -> ^(OPERATOR
	           INDEX[$l]
	           ^(ARGUMENT_LIST $postfixExpression expression)
	           RSQUARE)
	  |	// function call:
	    LPAREN argumentExpressionList RPAREN
	    -> ^(CALL LPAREN $postfixExpression ABSENT argumentExpressionList
	    	 RPAREN ABSENT)
	  |	// CUDA kernel function call:
	    LEXCON args1=argumentExpressionList REXCON 
	    LPAREN args2=argumentExpressionList RPAREN
	    -> ^(CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT)
	  | DOT IDENTIFIER
	    -> ^(DOT $postfixExpression IDENTIFIER)
	  | ARROW IDENTIFIER
	    -> ^(ARROW $postfixExpression IDENTIFIER)
	  | p=PLUSPLUS
	    -> ^(OPERATOR POST_INCREMENT[$p]
	         ^(ARGUMENT_LIST $postfixExpression))
	  //| // CIVL-C @ operator: remote reference like x@f
	    //AT IDENTIFIER
	    //-> ^(AT $postfixExpression IDENTIFIER)
	  | m=MINUSMINUS
	    -> ^(OPERATOR POST_DECREMENT[$m]
	         ^(ARGUMENT_LIST $postfixExpression))
	  )*
	;

/*
 * The "(typename) {...}" is a "compound literal".
 * See C11 Sec. 6.5.2.5.  I don't know what
 * it means when it ends with an extra COMMA.
 * I assume it doesn't mean anything and is just
 * allowed as a convenience for the poor C programmer
 * (but why?).
 *
 * Ambiguity: need to distinguish the compound literal
 * "(typename) {...}" from the primaryExpression
 * "(expression)".  Presence of '{' implies it must
 * be the compound literal.
 */
postfixExpressionRoot
	: (LPAREN typeName RPAREN LCURLY)=>
	  LPAREN typeName RPAREN LCURLY initializerList 
		( RCURLY
		| COMMA RCURLY
		)
	  -> ^(COMPOUND_LITERAL LPAREN typeName initializerList RCURLY)
	| primaryExpression
	;

/* 6.5.2 */
argumentExpressionList
	: -> ^(ARGUMENT_LIST)
	| assignmentExpression (COMMA assignmentExpression)*
	  -> ^(ARGUMENT_LIST assignmentExpression+)
	 ;

/* 6.5.3 */
unaryExpression
scope DeclarationScope;
@init {
  $DeclarationScope::isTypedef = false;
  $DeclarationScope::typedefNameUsed=false;
}
	: postfixExpression
	| p=PLUSPLUS unaryExpression
	  -> ^(OPERATOR PRE_INCREMENT[$p]
	       ^(ARGUMENT_LIST unaryExpression))
	| m=MINUSMINUS unaryExpression
	  -> ^(OPERATOR PRE_DECREMENT[$m]
	       ^(ARGUMENT_LIST unaryExpression))
	| unaryOperator castExpression
	  -> ^(OPERATOR unaryOperator ^(ARGUMENT_LIST castExpression))
	| (SIZEOF LPAREN typeName)=> SIZEOF LPAREN typeName RPAREN
	  -> ^(SIZEOF TYPE typeName)
	| SIZEOF unaryExpression
	  -> ^(SIZEOF EXPR unaryExpression)
	| SCOPEOF unaryExpression
	  -> ^(SCOPEOF unaryExpression)
	| ALIGNOF LPAREN typeName RPAREN
	  -> ^(ALIGNOF typeName)
	| spawnExpression
    | callsExpression
	;


/* CIVL $spawn expression */
spawnExpression
	: SPAWN postfixExpressionRoot LPAREN 
	  argumentExpressionList RPAREN 
	  -> ^(SPAWN LPAREN postfixExpressionRoot ABSENT
	       argumentExpressionList RPAREN)
	;

/* CIVL $calls expression */
callsExpression
	: CALLS LPAREN postfixExpressionRoot LPAREN 
	  argumentExpressionList RPAREN RPAREN
	  -> ^(CALLS LPAREN postfixExpressionRoot ABSENT
	       argumentExpressionList RPAREN)
	;


/* 6.5.3 */
unaryOperator
	: AMPERSAND | STAR | PLUS | SUB | TILDE | NOT | BIG_O
	;

/* 6.5.4 */
// ambiguity 1: (expr) is a unary expression and looks like (typeName).
// ambiguity 2: (typeName){...} is a compound literal and looks like cast
castExpression
scope DeclarationScope;
@init{
	$DeclarationScope::isTypedef = false;
	$DeclarationScope::typedefNameUsed=false;
}
	: (LPAREN typeName RPAREN ~LCURLY)=> l=LPAREN typeName RPAREN castExpression
	  -> ^(CAST typeName castExpression $l)
	| unaryExpression
	;
	
// TODO
remoteExpression
	:(castExpression -> castExpression)
	( AT y=castExpression
	  -> ^(OPERATOR AT ^(ARGUMENT_LIST $remoteExpression $y))
    )*
	;

/* 6.5.5 */
multiplicativeExpression
	: (remoteExpression -> remoteExpression)
	( STAR y=remoteExpression
	  -> ^(OPERATOR STAR ^(ARGUMENT_LIST $multiplicativeExpression $y))
	| DIV y=remoteExpression
	  -> ^(OPERATOR DIV ^(ARGUMENT_LIST $multiplicativeExpression $y))
    | MOD y=remoteExpression
	  -> ^(OPERATOR MOD ^(ARGUMENT_LIST $multiplicativeExpression $y))
    )*
	;

/* 6.5.6 */
additiveExpression
	: (multiplicativeExpression -> multiplicativeExpression)
        ( PLUS y=multiplicativeExpression
          -> ^(OPERATOR PLUS ^(ARGUMENT_LIST $additiveExpression $y))
        | SUB y=multiplicativeExpression
          -> ^(OPERATOR SUB ^(ARGUMENT_LIST $additiveExpression $y))
        )*
	;

/* CIVL-C range expression "lo .. hi" or "lo .. hi # step" */
// a + b .. c + d is equivalent to (a + b) .. (c + d)
rangeExpression
	: (additiveExpression -> additiveExpression)
      ( DOTDOT y=additiveExpression
        ( -> ^(DOTDOT $rangeExpression $y)
        | HASH z=additiveExpression
          -> ^(DOTDOT $rangeExpression $y $z)
        )
      )?
    ;

/* 6.5.7 */
shiftExpression
	: (rangeExpression -> rangeExpression)
        ( SHIFTLEFT y=rangeExpression
          -> ^(OPERATOR SHIFTLEFT ^(ARGUMENT_LIST $shiftExpression $y))
        | SHIFTRIGHT y=rangeExpression
          -> ^(OPERATOR SHIFTRIGHT ^(ARGUMENT_LIST $shiftExpression $y))
        )*
	;

/* 6.5.8 */
relationalExpression
	: ( shiftExpression -> shiftExpression )
	  ( relationalOperator y=shiftExpression
	    -> ^(OPERATOR relationalOperator ^(ARGUMENT_LIST $relationalExpression $y))
	  )*
	;

relationalOperator
	: LT | GT | LTE | GTE
	;

/* 6.5.9 */
equalityExpression
	: ( relationalExpression -> relationalExpression )
	  ( equalityOperator y=relationalExpression
	    -> ^(OPERATOR equalityOperator ^(ARGUMENT_LIST $equalityExpression $y))
	  )*
	;

equalityOperator
	: EQUALS | NEQ
	;

/* 6.5.10 */
andExpression
	: ( equalityExpression -> equalityExpression )
	  ( AMPERSAND y=equalityExpression
	    -> ^(OPERATOR AMPERSAND ^(ARGUMENT_LIST $andExpression $y))
	  )*
	;

/* 6.5.11 */
exclusiveOrExpression
	: ( andExpression -> andExpression )
	  ( BITXOR y=andExpression
	    -> ^(OPERATOR BITXOR ^(ARGUMENT_LIST $exclusiveOrExpression $y))
	  )*
	;

/* 6.5.12 */
inclusiveOrExpression
	: ( exclusiveOrExpression -> exclusiveOrExpression )
	  ( BITOR y=exclusiveOrExpression
	    -> ^(OPERATOR BITOR ^(ARGUMENT_LIST $inclusiveOrExpression $y))
	  )*
	;

/* 6.5.13 */
logicalAndExpression
	: ( inclusiveOrExpression -> inclusiveOrExpression )
	  ( AND y=inclusiveOrExpression
	    -> ^(OPERATOR AND ^(ARGUMENT_LIST $logicalAndExpression $y))
	  )*
	;

/* 6.5.14 */
logicalOrExpression
	: ( logicalAndExpression -> logicalAndExpression )
	  ( OR y=logicalAndExpression
	    -> ^(OPERATOR OR ^(ARGUMENT_LIST $logicalOrExpression $y))
	  )*
	;
	
/* Added for CIVL-C.  Usually 6.5.15 would use logicalOrExpression. */
logicalImpliesExpression
	: ( logicalOrExpression -> logicalOrExpression )
	  ( IMPLIES y=logicalOrExpression
	    -> ^(OPERATOR IMPLIES ^(ARGUMENT_LIST $logicalImpliesExpression $y))
	  )*
    	;

/* 6.5.15 */
conditionalExpression
	: logicalImpliesExpression
	( -> logicalImpliesExpression
    	| QMARK expression COLON conditionalExpression
    	  -> ^(OPERATOR QMARK
    	       ^(ARGUMENT_LIST
    	         logicalImpliesExpression
    	         expression
    	         conditionalExpression))
    	)
	;

/* A CIVL-C quantified expression using $exists or $forall.
 */
quantifierExpression
	: quantifier LCURLY type=typeName id=IDENTIFIER
	  BITOR restrict=conditionalExpression RCURLY 
	  cond=assignmentExpression
	  -> ^(quantifier $type $id $restrict $cond)
	| quantifier LCURLY id=IDENTIFIER ASSIGN
	  lower=additiveExpression DOTDOT upper=additiveExpression
	  RCURLY cond=assignmentExpression
	  -> ^(quantifier $id $lower $upper $cond)
// eventually change to the following:
//	| quantifier LCURLY id=IDENTIFIER ASSIGN rangeExpression
//	  RCURLY cond=assignmentExpression
//	  -> ^(quantifier $id rangeExpression $cond)
	;

/* One of the CIVL-C first-order quantifiers.
 * UNIFORM represents uniform continuity.  
 */	
quantifier
	: FORALL | EXISTS | UNIFORM
	;

/* 6.5.16
 * conditionalExpression or
 * Root: OPERATOR
 * Child 0: assignmentOperator
 * Child 1: ARGUMENT_LIST
 * Child 1.0: unaryExpression
 * Child 1.1: assignmentExpression
 */
assignmentExpression
	: (unaryExpression assignmentOperator)=>
	  unaryExpression assignmentOperator assignmentExpression
	  -> ^(OPERATOR assignmentOperator
	       ^(ARGUMENT_LIST unaryExpression assignmentExpression))
	| conditionalExpression
	| quantifierExpression
	;

/* 6.5.16 */
assignmentOperator
	: ASSIGN | STAREQ | DIVEQ | MODEQ | PLUSEQ | SUBEQ
	| SHIFTLEFTEQ | SHIFTRIGHTEQ | BITANDEQ | BITXOREQ | BITOREQ
	;

/* 6.5.17
 * assignmentExpression or
 * Root: OPERATOR
 * Child 0: COMMA
 * Child 1: ARGUMENT_LIST
 * Child 1.0: arg0
 * Child 1.1: arg1
 */
commaExpression
	: ( assignmentExpression -> assignmentExpression )
	  ( COMMA y=assignmentExpression
	    -> ^(OPERATOR COMMA ^(ARGUMENT_LIST $commaExpression $y))
	  )*
	;

/* The most general class of expressions.
 * Includes a CIVL-C "collective" expression,
 * and all expressions defined previously.
 */
expression
	: COLLECTIVE LPAREN proc=conditionalExpression
	   RPAREN body=conditionalExpression
	  -> ^(COLLECTIVE $proc $body)
	| commaExpression
	;
			

/* 6.6 */
constantExpression
	: conditionalExpression
	;
	

/* ***** A.2.2: Declarations ***** */

/* 6.7.
 *
 * This rule will construct either a DECLARATION, or
 * STATICASSERT tree:
 *
 * Root: DECLARATION
 * Child 0: declarationSpecifiers
 * Child 1: initDeclaratorList or ABSENT
 * Child 2: contract or ABSENT
 *
 * Root: STATICASSERT
 * Child 0: constantExpression
 * Child 1: stringLiteral
 *
 * The declarationSpecifiers rule returns a bit telling whether
 * "typedef" occurred among the specifiers.  This bit is passed 
 * to the initDeclaratorList rule, and down the call chain,
 * where eventually an IDENTIFIER should be reached.  At that point,
 * if the bit is true, the IDENTIFIER is added to the set of typedef
 * names.
 */
declaration
scope DeclarationScope;
@init {
  $DeclarationScope::isTypedef = false;
  $DeclarationScope::typedefNameUsed=false;
}
	: d=declarationSpecifiers
	  ( 
	    i=initDeclaratorList contract SEMI
	    -> ^(DECLARATION $d $i contract)
	  | SEMI
	    -> ^(DECLARATION $d ABSENT ABSENT)
	  )
	| staticAssertDeclaration
	;


/* 6.7
 * Root: DECLARATION_SPECIFIERS
 * Children: declarationSpecifier (any number)
 */
declarationSpecifiers
	: l=declarationSpecifierList
	  -> ^(DECLARATION_SPECIFIERS declarationSpecifierList)
	;

/* Tree: flat list of declarationSpecifier
 */
declarationSpecifierList
	: (
	    {!$DeclarationScope::isTypedef || input.LT(2).getType() != SEMI }?
	    s=declarationSpecifier
	  )+
	;

declarationSpecifier
	: s=storageClassSpecifier
	| typeSpecifierOrQualifier
	| functionSpecifier
	| alignmentSpecifier
	;

/* 
 * I factored this out of the declarationSpecifiers rule
 * to deal with the ambiguity of "ATOMIC" in one place.
 * "ATOMIC ( typeName )" matches atomicTypeSpecifier, which
 * is a typeSpecifier. "ATOMIC" matches typeQualifier.
 * When you see "ATOMIC" all you have to do is look at the
 * next token. If it's '(', typeSpecifier is it.
 */
typeSpecifierOrQualifier
	: (typeSpecifier)=> typeSpecifier
        | typeQualifier
	;

/* 6.7
 * Root: INIT_DECLARATOR_LIST
 * Children: initDeclarator
 */
initDeclaratorList
	: i+=initDeclarator (COMMA i+=initDeclarator)*
	  -> ^(INIT_DECLARATOR_LIST $i+)
	;

/* 6.7
 * Root: INIT_DECLARATOR
 * Child 0: declarator
 * Child 1: initializer or ABSENT
 */
initDeclarator
	: d=declarator
	  (  -> ^(INIT_DECLARATOR $d ABSENT)
	  | (ASSIGN i=initializer) -> ^(INIT_DECLARATOR $d $i)
	  )
	;

/* 6.7.1 */
storageClassSpecifier
	: TYPEDEF {$DeclarationScope::isTypedef = true;}
	| (EXTERN | STATIC | THREADLOCAL | AUTO | REGISTER | SHARED)
	;

/* 6.7.2 */
typeSpecifier
	: VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE
	| SIGNED | UNSIGNED | BOOL | COMPLEX | REAL | RANGE
	| atomicTypeSpecifier
	| structOrUnionSpecifier
	| enumSpecifier
	| typedefName
	| domainSpecifier
    	| typeofSpecifier
	;

/* GNU C extension: 
 * 6.6 Referring to a Type with typeof
 * Another way to refer to the type of an expression is with typeof. 
 * The syntax of using of this keyword looks like sizeof, but the construct acts 
 * semantically like a type name defined with typedef.
 * There are two ways of writing the argument to typeof: with an expression or with a type. 
 * Here is an example with an expression:
 *   typeof (x[0](1))
 * This assumes that x is an array of pointers to functions; the type described is that of 
 * the values of the functions.
 * Here is an example with a typename as the argument:
 *   typeof (int *)
 * */
typeofSpecifier
    : TYPEOF LPAREN
        ( commaExpression RPAREN
          -> ^(TYPEOF_EXPRESSION LPAREN commaExpression RPAREN)
        | typeName RPAREN
          -> ^(TYPEOF_TYPE LPAREN typeName RPAREN)
        )
    ;

/* 6.7.2.1
 * Root: STRUCT or UNION
 * Child 0: IDENTIFIER (the tag) or ABSENT
 * Child 1: structDeclarationList or ABSENT
 */
structOrUnionSpecifier
	: structOrUnion
	    ( IDENTIFIER LCURLY structDeclarationList RCURLY
	      -> ^(structOrUnion IDENTIFIER structDeclarationList RCURLY)
	    | LCURLY structDeclarationList RCURLY
	      -> ^(structOrUnion ABSENT structDeclarationList RCURLY)
	    | IDENTIFIER
	      -> ^(structOrUnion IDENTIFIER ABSENT)
	    )
	;

/* 6.7.2.1 */
structOrUnion
	: STRUCT | UNION
	;

/* 6.7.2.1
 * Root: STRUCT_DECLARATION_LIST
 * Children: structDeclaration
 */
structDeclarationList
	: structDeclaration*
	  -> ^(STRUCT_DECLARATION_LIST structDeclaration*)
	;

/* 6.7.2.1
 * Two possible trees:
 *
 * Root: STRUCT_DECLARATION
 * Child 0: specifierQualifierList
 * Child 1: structDeclaratorList or ABSENT
 *
 * or
 *
 * staticAssertDeclaration (root: STATICASSERT)
 */
structDeclaration
scope DeclarationScope;
@init {
  $DeclarationScope::isTypedef = false;
  $DeclarationScope::typedefNameUsed = false;
}
    : s=specifierQualifierList
      ( -> ^(STRUCT_DECLARATION $s ABSENT)
      | structDeclaratorList
        -> ^(STRUCT_DECLARATION $s structDeclaratorList)
      )
      SEMI
    | staticAssertDeclaration
    ;

/* 6.7.2.1
 * Root: SPECIFIER_QUALIFIER_LIST
 * Children: typeSpecifierOrQualifier
 */
specifierQualifierList
    : typeSpecifierOrQualifier+
      -> ^(SPECIFIER_QUALIFIER_LIST typeSpecifierOrQualifier+)
    ;

/* 6.7.2.1
 * Root: STRUCT_DECLARATOR_LIST
 * Children: structDeclarator (at least 1)
 */
structDeclaratorList
    : s+=structDeclarator (COMMA s+=structDeclarator)*
      -> ^(STRUCT_DECLARATOR_LIST $s+)
    ;

/* 6.7.2.1
 * Root: STRUCT_DECLARATOR
 * Child 0: declarator or ABSENT
 * Child 1: constantExpression or ABSENT
 */
structDeclarator
    : declarator
      (  -> ^(STRUCT_DECLARATOR declarator ABSENT)
      | COLON constantExpression
         -> ^(STRUCT_DECLARATOR declarator constantExpression)
      )
    | COLON constantExpression
      -> ^(STRUCT_DECLARATOR ABSENT constantExpression)
    ;

/* 6.7.2.2
 * Root: ENUM
 * Child 0: IDENTIFIER (tag) or ABSENT
 * Child 1: enumeratorList
 */
enumSpecifier
    : ENUM 
        ( IDENTIFIER 
          -> ^(ENUM IDENTIFIER ABSENT)
        | IDENTIFIER LCURLY enumeratorList COMMA? RCURLY
          -> ^(ENUM IDENTIFIER enumeratorList)
        | LCURLY enumeratorList COMMA? RCURLY
          -> ^(ENUM ABSENT enumeratorList)
        )
    ;

/* 6.7.2.2
 * Root: ENUMERATOR_LIST
 * Children: enumerator
 */
enumeratorList
    : enumerator (COMMA enumerator)*
      -> ^(ENUMERATOR_LIST enumerator+)
    ;

/* 6.7.2.2
 * Root: ENUMERATOR
 * Child 0: IDENTIFIER
 * Child 1: constantExpression or ABSENT
 */
enumerator
	: IDENTIFIER
    	  {
    		$Symbols::enumerationConstants.add($IDENTIFIER.text);
		// System.err.println("define enum constant "+$IDENTIFIER.text);	
    	  }
    	  (  -> ^(ENUMERATOR IDENTIFIER ABSENT)
    	  | (ASSIGN constantExpression)
    	     -> ^(ENUMERATOR IDENTIFIER constantExpression)
    	  )
	;

/* 6.7.2.4 */
atomicTypeSpecifier
    : ATOMIC LPAREN typeName RPAREN
      -> ^(ATOMIC typeName)
    ;

/* 6.7.3 */
typeQualifier
    : CONST | RESTRICT | VOLATILE | ATOMIC | INPUT | OUTPUT
    ;

/* 6.7.4.  Added CIVL $atomic and $atom as specifiers, indicating
 * a function should be executed atomically or atom-ly.  CIVL's
 * $abstract specifier also included for abstract functions.
 */
functionSpecifier
    : INLINE | NORETURN
    | ABSTRACT CONTIN LPAREN INTEGER_CONSTANT RPAREN 
      -> ^(ABSTRACT INTEGER_CONSTANT)
    | ABSTRACT -> ^(ABSTRACT)
    | SYSTEM  -> ^(SYSTEM)
    | FATOMIC -> ^(FATOMIC)
    | PURE -> ^(PURE)
    | DEVICE
    | GLOBAL
    ;

/* 6.7.5
 * Root: ALIGNAS
 * Child 0: TYPE or EXPR 
 * Child 1: typeName (if Child 0 is TYPE) or constantExpression
 *          (if Child 0 is EXPR)
 */
alignmentSpecifier
    : ALIGNAS LPAREN 
        ( typeName RPAREN
          -> ^(ALIGNAS TYPE typeName)
        | constantExpression RPAREN
          -> ^(ALIGNAS EXPR constantExpression)
        )
    ;
	
/* 6.7.6
 * Root: DECLARATOR
 * Child 0: pointer or ABSENT
 * Child 1: directDeclarator
 */
declarator
	: d=directDeclarator
	  -> ^(DECLARATOR ABSENT $d)
	| pointer d=directDeclarator
	  -> ^(DECLARATOR pointer $d)
	;

/* 6.7.6
 * Root: DIRECT_DECLARATOR
 * Child 0: directDeclaratorPrefix 
 * Children 1..: list of directDeclaratorSuffix (may be empty)
 */
directDeclarator
	: p=directDeclaratorPrefix
	  ( -> ^(DIRECT_DECLARATOR $p)
	  | s+=directDeclaratorSuffix+ ->^(DIRECT_DECLARATOR $p $s+)
	  )
	;

/*
 * Tree: either an IDENTIFIER or a declarator.
 */
directDeclaratorPrefix
	: IDENTIFIER 
		{
			if ($DeclarationScope::isTypedef) {
				$Symbols::types.add($IDENTIFIER.text);
                //System.err.println("define type "+$IDENTIFIER.text);
			}else{
                //$Symbols::types.remove($IDENTIFIER.text);
            }
		}
	| LPAREN! declarator RPAREN!
	;


directDeclaratorSuffix
	: directDeclaratorArraySuffix
	| directDeclaratorFunctionSuffix
	;

/*
 * Root: ARRAY_SUFFIX
 * child 0: LSQUARE (for source information)
 * child 1: STATIC or ABSENT
 * child 2: TYPE_QUALIFIER_LIST
 * child 3: expression (array extent), 
 *          "*" (unspecified variable length), or ABSENT
 * child 4: RSQUARE (for source information)
 */
directDeclaratorArraySuffix
	: LSQUARE
	  ( typeQualifierList_opt assignmentExpression_opt RSQUARE
	    -> ^(ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt
	         assignmentExpression_opt RSQUARE)
	  | STATIC typeQualifierList_opt assignmentExpression RSQUARE
	    -> ^(ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt
	         assignmentExpression RSQUARE)
	  |   typeQualifierList STATIC assignmentExpression RSQUARE
	    -> ^(ARRAY_SUFFIX LSQUARE STATIC typeQualifierList
	         assignmentExpression RSQUARE)
	  |   typeQualifierList_opt STAR RSQUARE
	    -> ^(ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt
	         STAR RSQUARE)
	  )
	;

/*
 * Root: FUNCTION_SUFFIX
 * child 0: LPAREN (for source information)
 * child 1: either parameterTypeList or identifierList or ABSENT
 * child 2: RPAREN (for source information)
 */
directDeclaratorFunctionSuffix
scope DeclarationScope;
@init {
    $DeclarationScope::isTypedef = false;
    $DeclarationScope::typedefNameUsed = false;
}
	: LPAREN
	  ( parameterTypeList RPAREN 
	    -> ^(FUNCTION_SUFFIX LPAREN parameterTypeList  RPAREN)
	  | identifierList RPAREN
	    -> ^(FUNCTION_SUFFIX LPAREN identifierList RPAREN)
	  | RPAREN -> ^(FUNCTION_SUFFIX LPAREN ABSENT RPAREN)
	  )
	;

/*
 * Root: TYPE_QUALIFIER_LIST
 * Children: typeQualifier
 */
typeQualifierList_opt
	: typeQualifier* -> ^(TYPE_QUALIFIER_LIST typeQualifier*)
	;

/*
 * Tree: assignmentExpression or ABSENT
 */
assignmentExpression_opt
	:  -> ABSENT
	| assignmentExpression
	;

/* 6.7.6 
 * Root: POINTER
 * children: STAR
 */
pointer
    : pointer_part+ -> ^(POINTER pointer_part+)
    ;

/*
 * Root: STAR
 * child 0: TYPE_QUALIFIER_LIST
 */
pointer_part
	: STAR typeQualifierList_opt
	-> ^(STAR typeQualifierList_opt)
	;

/* 6.7.6
 * Root: TYPE_QUALIFIER_LIST
 * children: typeQualifier
 */
typeQualifierList
    : typeQualifier+ -> ^(TYPE_QUALIFIER_LIST typeQualifier+)
    ;

/* 6.7.6 
 * Root: PARAMETER_TYPE_LIST
 * child 0: parameterList (at least 1 parameter declaration)
 * child 1: ELLIPSIS or ABSENT
 * 
 * If the parameterTypeList occurs in a function prototype
 * (that is not part of a function definition), it defines
 * a new scope (a "function prototype scope").  If it occurs
 * in a function definition, it does not define a new scope. 
 */
 
parameterTypeList
	: {$Symbols::isFunctionDefinition}? parameterTypeListWithoutScope
	| parameterTypeListWithScope
	;

parameterTypeListWithScope
scope Symbols;
@init {
	$Symbols::types = new HashSet<String>();
	$Symbols::enumerationConstants = new HashSet<String>();
	$Symbols::isFunctionDefinition = false;
}
	: parameterTypeListWithoutScope
	;

parameterTypeListWithoutScope
    : parameterList
      ( -> ^(PARAMETER_TYPE_LIST parameterList ABSENT)
      | COMMA ELLIPSIS
        -> ^(PARAMETER_TYPE_LIST parameterList ELLIPSIS)
      )
    ;

/* 6.7.6
 * Root: PARAMETER_LIST
 * children: parameterDeclaration
 */
parameterList
    : parameterDeclaration (COMMA parameterDeclaration)*
      -> ^(PARAMETER_LIST parameterDeclaration+)
    ;

/* 6.7.6 
 * Root: PARAMETER_DECLARATION
 * Child 0: declarationSpecifiers
 * Child 1: declarator, or abstractDeclarator, or ABSENT
 */
parameterDeclaration
scope DeclarationScope;
@init {
    $DeclarationScope::isTypedef = false;
    $DeclarationScope::typedefNameUsed = false;
    //System.err.println("parameter declaration start");
}
    : declarationSpecifiers
      ( -> ^(PARAMETER_DECLARATION declarationSpecifiers ABSENT)
      | declaratorOrAbstractDeclarator
        -> ^(PARAMETER_DECLARATION
             declarationSpecifiers declaratorOrAbstractDeclarator)
      )
    ;


// this has non-LL* decision due to recursive rule invocations
// reachable from alts 1,2...  E.g., both can start with pointer.
declaratorOrAbstractDeclarator
	:	(declarator)=> declarator
	|	abstractDeclarator
	;
	

/* 6.7.6
 * Root: IDENTIFIER_LIST
 * children: IDENTIFIER (at least 1)
 */
identifierList
    : IDENTIFIER ( COMMA IDENTIFIER )*
      -> ^(IDENTIFIER_LIST IDENTIFIER+)
    ;

/* 6.7.6.  This is how a type is described without attaching
 * it to an identifier.
 * Root: TYPE_NAME
 * child 0: specifierQualifierList
 * child 1: abstractDeclarator or ABSENT
 */
typeName
    : specifierQualifierList
      ( -> ^(TYPE_NAME specifierQualifierList ABSENT)
      | abstractDeclarator
        -> ^(TYPE_NAME specifierQualifierList abstractDeclarator)
      )
    ;

/* 6.7.7.  Abstract declarators are like declarators without
 * the IDENTIFIER.
 *
 * Root: ABSTRACT_DECLARATOR
 * Child 0. pointer (may be ABSENT).  Some number of *s with possible
 *   type qualifiers.
 * Child 1. directAbstractDeclarator (may be ABSENT). 
 */
abstractDeclarator
    : pointer
      -> ^(ABSTRACT_DECLARATOR pointer ABSENT)
    | directAbstractDeclarator
      -> ^(ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator)
    | pointer directAbstractDeclarator
      -> ^(ABSTRACT_DECLARATOR pointer directAbstractDeclarator)
    ;

/* 6.7.7
 *
 * Root: DIRECT_ABSTRACT_DECLARATOR
 * Child 0. abstract declarator or ABSENT.  
 * Children 1..: any number of direct abstract declarator suffixes
 *
 * Note that the difference between this and a directDeclarator
 * is that Child 0 of a direct declarator would be either
 * an IDENTIFIER or a declarator, but never ABSENT.
 */
directAbstractDeclarator
    : LPAREN abstractDeclarator RPAREN directAbstractDeclaratorSuffix*
      -> ^(DIRECT_ABSTRACT_DECLARATOR abstractDeclarator
           directAbstractDeclaratorSuffix*)
    | directAbstractDeclaratorSuffix+
      -> ^(DIRECT_ABSTRACT_DECLARATOR ABSENT directAbstractDeclaratorSuffix+)
    ;


/* 6.7.8 
 * Root: TYPEDEF_NAME
 * Child 0: IDENTIFIER
 *
 * Ambiguity: example:
 * typedef int foo;
 * typedef int foo;
 *
 * This is perfectly legal: you can define a typedef twice
 * as long as both definitions are equivalent.  However,
 * the first definition causes foo to be entered into the type name
 * table, so when parsing the second definition, foo is 
 * interpreted as a typedefName (a type specifier), and the
 * declaration would have empty declarator.   This is not
 * what you want, so you have to forbid it somehow.  I do this
 * by requiring that if you are "in" a typedef, a typedef name
 * cannot be immediately followed by a semicolon.  This is sound
 * because the C11 Standard requires at least one declarator
 * to be present in a typedef.  See declarationSpecifierList.
 */
typedefName
@after{
    if(!$DeclarationScope::typedefNameUsed)
    	$DeclarationScope::typedefNameUsed=true;
} 
    : {!$DeclarationScope::typedefNameUsed && isTypeName(input.LT(1).getText())}?
      IDENTIFIER
      -> ^(TYPEDEF_NAME IDENTIFIER)
    ;

/* 6.7.7
 * Two possibilities:
 *
 * Root: ARRAY_SUFFIX
 * Child 0: STATIC or ABSENT
 * Child 1: typeQualifierList or ABSENT
 * Child 2: expression or STAR or ABSENT
 *
 * Root: FUNCTION_SUFFIX
 * Child 0: parameterTypeList or ABSENT
 */
directAbstractDeclaratorSuffix
    : LSQUARE
      ( typeQualifierList_opt assignmentExpression_opt RSQUARE
        -> ^(ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt
             assignmentExpression_opt)
      | STATIC typeQualifierList_opt assignmentExpression RSQUARE
        -> ^(ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt
             assignmentExpression)
      | typeQualifierList STATIC assignmentExpression RSQUARE
        -> ^(ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression)
      | STAR RSQUARE
        -> ^(ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR)
      )
    | LPAREN
      ( parameterTypeList RPAREN
        -> ^(FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN)
      | RPAREN
        -> ^(FUNCTION_SUFFIX LPAREN ABSENT RPAREN)
      )
    ;

/* 6.7.9 */
initializer
    : assignmentExpression -> ^(SCALAR_INITIALIZER assignmentExpression)
    | LCURLY initializerList
        (   RCURLY
        |   COMMA RCURLY
        )
      -> initializerList
    ;

/* 6.7.9 */
initializerList
    : designatedInitializer (COMMA designatedInitializer)*
      -> ^(INITIALIZER_LIST designatedInitializer+)
    ;

designatedInitializer
	: initializer
	  -> ^(DESIGNATED_INITIALIZER ABSENT initializer)
	| designation initializer
	  -> ^(DESIGNATED_INITIALIZER designation initializer)
	;

/* 6.7.9 */
designation
    : designatorList ASSIGN -> ^(DESIGNATION designatorList)
    ;

/* 6.7.9 */
designatorList
    : designator+
    ;

/* 6.7.9 */
designator
    : LSQUARE constantExpression RSQUARE
      -> ^(ARRAY_ELEMENT_DESIGNATOR constantExpression)
    | DOT IDENTIFIER
      -> ^(FIELD_DESIGNATOR IDENTIFIER)
    ;

/* 6.7.10 */
staticAssertDeclaration
    : STATICASSERT LPAREN constantExpression COMMA STRING_LITERAL
      RPAREN SEMI
      -> ^(STATICASSERT constantExpression STRING_LITERAL)
    ;

/* CIVL-C $domain or $domain(n) type */
domainSpecifier
	: DOMAIN
	  ( -> ^(DOMAIN)
	  | LPAREN INTEGER_CONSTANT RPAREN -> ^(DOMAIN INTEGER_CONSTANT RPAREN)
	  )
	;


/* ***** A.2.3: Statements ***** */

/* 6.8 */
statement
    : labeledStatement -> ^(STATEMENT labeledStatement)
    | compoundStatement -> ^(STATEMENT compoundStatement)
    | expressionStatement -> ^(STATEMENT expressionStatement)
    | selectionStatement -> ^(STATEMENT selectionStatement)
    | iterationStatement -> ^(STATEMENT iterationStatement)
    | jumpStatement -> ^(STATEMENT jumpStatement)
//    | pragma -> ^(STATEMENT pragma)
    | whenStatement -> ^(STATEMENT whenStatement)
    | chooseStatement -> ^(STATEMENT chooseStatement)
    | atomicStatement -> ^(STATEMENT atomicStatement)
    | datomicStatement -> ^(STATEMENT datomicStatement)
    ;

statementWithScope
scope Symbols;
@init {
	$Symbols::types = new HashSet<String>();
	$Symbols::enumerationConstants = new HashSet<String>();
        $Symbols::isFunctionDefinition = false;
}
	: statement
	;

/* 6.8.1
 * Three possible trees:
 *
 * Root: IDENTIFIER_LABELED_STATEMENT
 * Child 0: IDENTIFIER
 * Child 1: statement
 *
 * Root: CASE_LABELED_STATEMENT
 * Child 0: CASE
 * Child 1: constantExpression
 * Child 2: statement
 *
 * Root: DEFAULT_LABELED_STATEMENT
 * Child 0: DEFAULT
 * Child 1: statement
 */
labeledStatement
    : IDENTIFIER COLON statement
      -> ^(IDENTIFIER_LABELED_STATEMENT IDENTIFIER statement)
    | CASE constantExpression COLON statement
      -> ^(CASE_LABELED_STATEMENT CASE constantExpression statement)
    | DEFAULT COLON statement
      -> ^(DEFAULT_LABELED_STATEMENT DEFAULT statement)
    ;

/* 6.8.2
 * Root: BLOCK
 * Child 0: LCURLY (for source information)
 * Child 1: blockItemList or ABSENT
 * Child 2: RCURLY (for source information)
 */
compoundStatement
scope Symbols;
scope DeclarationScope;
@init {
	$Symbols::types = new HashSet<String>();
	$Symbols::enumerationConstants = new HashSet<String>();
        $Symbols::isFunctionDefinition = false;
        $DeclarationScope::isTypedef = false;
        $DeclarationScope::typedefNameUsed = false;	
}
    : LCURLY
      ( RCURLY
        -> ^(COMPOUND_STATEMENT LCURLY ABSENT RCURLY)
      | blockItemList RCURLY
        -> ^(COMPOUND_STATEMENT LCURLY blockItemList RCURLY)
      )
    ;

/* 6.8.2 */
blockItemList
    : blockItem+ -> ^(BLOCK_ITEM_LIST blockItem+)
    ;



/* 6.8.3
 * Root: EXPRESSION_STATEMENT
 * Child 0: expression or ABSENT
 * Child 1: SEMI (for source information)
 */
expressionStatement
    : expression SEMI -> ^(EXPRESSION_STATEMENT expression SEMI)
    | SEMI -> ^(EXPRESSION_STATEMENT ABSENT SEMI)
    ;

/* 6.8.4
 * Two possible trees:
 *
 * Root: IF
 * Child 0: expression
 * Child 1: statement (true branch)
 * Child 2: statement or ABSENT (false branch)
 *
 * Root: SWITCH
 * Child 0: expression
 * Child 1: statement
 */
selectionStatement
scope Symbols;
@init {
	$Symbols::types = new HashSet<String>();
	$Symbols::enumerationConstants = new HashSet<String>();
        $Symbols::isFunctionDefinition = false;
}
    : IF LPAREN expression RPAREN s1=statementWithScope
        ( (ELSE)=> ELSE s2=statementWithScope
          -> ^(IF expression $s1 $s2)
        | -> ^(IF expression $s1 ABSENT)
        )
    | SWITCH LPAREN expression RPAREN s=statementWithScope
      -> ^(SWITCH expression $s)
    ;

/* 6.8.5
 * Three possible trees:
 *
 * Root: WHILE
 * Child 0: expression
 * Child 1: statement
 *
 * Root: DO
 * Child 0: statement
 * Child 1: expression
 *
 * Root: FOR
 * Child 0: clause-1: declaration, expression, or ABSENT
 *          (for loop initializer)
 * Child 1: expression or ABSENT (condition)
 * Child 2: expression or ABSENT (incrementer)
 * Child 3: statement (body)
 *
 */
iterationStatement
scope Symbols;
@init {
	$Symbols::types = new HashSet<String>();
	$Symbols::enumerationConstants = new HashSet<String>();
        $Symbols::isFunctionDefinition = false;
}
	: WHILE LPAREN expression RPAREN invariant_opt 
	  s=statementWithScope
	  -> ^(WHILE expression $s invariant_opt)
	| DO s=statementWithScope WHILE LPAREN expression RPAREN 
	  invariant_opt SEMI
	  -> ^(DO $s expression invariant_opt)
	| FOR LPAREN 
	  ( 
	    d=declaration e1=expression_opt SEMI e2=expression_opt
	    RPAREN i=invariant_opt s=statementWithScope
	    -> ^(FOR $d $e1 $e2 $s $i)
	  | e0=expression_opt SEMI e1=expression_opt SEMI
	    e2=expression_opt RPAREN i=invariant_opt
	    s=statementWithScope
	    -> ^(FOR $e0 $e1 $e2 $s $i)
	  )
	| (f=CIVLFOR | f=PARFOR) LPAREN
	    t=typeName_opt v=identifierList COLON e=expression RPAREN
	    i=invariant_opt s=statementWithScope
	    -> ^($f $t $v $e $s $i)
	;

expression_opt
	:	expression
	|	-> ABSENT
	;

invariant_opt
	:	-> ABSENT
	|	INVARIANT LPAREN expression RPAREN
		-> ^(INVARIANT expression)
	;

typeName_opt
	:	typeName
	|	-> ABSENT
	;

/* 6.8.6
 * Four possible trees:
 *
 * Root: GOTO
 * Child 0: IDENTIFIER
 * Child 1: SEMI (for source information)
 *
 * Root: CONTINUE
 * Child 0: SEMI (for source information)
 * 
 * Root: BREAK
 * Child 0: SEMI (for source information)
 *
 * Root: RETURN
 * Child 0: expression or ABSENT 
 * Child 1: SEMI (for source information)
 */
jumpStatement
    : GOTO IDENTIFIER SEMI -> ^(GOTO IDENTIFIER SEMI)
    | CONTINUE SEMI -> ^(CONTINUE SEMI)
    | BREAK SEMI -> ^(BREAK SEMI)
    | RETURN expression_opt SEMI -> ^(RETURN expression_opt SEMI)
    ;

/*
 * A pragma, which is represented as an identifier
 * (the first token following # pragma), followed
 * by a sequence of tokens.
 *
 * Root: PRAGMA
 * child 0: IDENTIFIER (first token following # pragma)
 * child 1: TOKEN_LIST (chilren are list of tokens following identifier)
 * child 2: NEWLINE (character which ends the pragma)
 */
pragma
    : PRAGMA IDENTIFIER NEWLINE
        -> ^(PRAGMA IDENTIFIER ^(TOKEN_LIST) NEWLINE)
    | PRAGMA IDENTIFIER pragmaBody NEWLINE
        -> ^(PRAGMA IDENTIFIER ^(TOKEN_LIST pragmaBody) NEWLINE)
	;

/* A pragma body, which is any sequence of tokens not 
 * containing NEWLINE, used in pragma rule.
 */
pragmaBody
	:	(~ NEWLINE)+
	;

/* CIVL-C $when statement.  This is a guarded command.
 * Syntax: $when (expr) stmt, where expr is a boolean
 * expression (guard).
 *
 * Root: WHEN
 * Child 0: expression
 * Child 1: statement
 */
whenStatement
	:	WHEN LPAREN expression RPAREN statement
		-> ^(WHEN expression statement)
	;

/* CIVL-C $choose statement.  This is a non-deterministic
 * selection statement.  Syntax: $choose { stmt stmt ... }.
 *
 * Root: CHOOSE
 * Children: 1 or more statement
 */
chooseStatement
	:	CHOOSE LCURLY statement+ RCURLY 
		-> ^(CHOOSE statement+)
	;

/* CIVL-C $atomic statement.  Syntax:
 * $atomic stmt.
 *
 * Root: CIVLATOMIC
 * Child 0: statement
 */
atomicStatement
	:	CIVLATOMIC s=statementWithScope
		-> ^(CIVLATOMIC $s)
	;

/* CIVL-C $atom statement.  Syntax:
 * $atom stmt.
 *
 * Root: CIVLATOM
 * Child 0: statement
 */
datomicStatement
	:	CIVLATOM s=statementWithScope
		-> ^(CIVLATOM $s)
	;

/* 6.9.1
 *
 * Root: FUNCTION_DEFINITION
 * Child 0: declarationSpecifiers
 * Child 1: declarator
 * Child 2: declarationList or ABSENT (formal parameters)
 * Child 3: compound statement (body)
 * Child 4: contract
 */
functionDefinition
scope Symbols; // "function scope"
scope DeclarationScope;
@init {
    $Symbols::types = new HashSet<String>();
    $Symbols::enumerationConstants = new HashSet<String>();
    $Symbols::isFunctionDefinition = true;
    $DeclarationScope::isTypedef = false;
    $DeclarationScope::typedefNameUsed=false;
}
	: declarator
	  contract
	  declarationList_opt
	  compoundStatement
	  -> ^(FUNCTION_DEFINITION ^(DECLARATION_SPECIFIERS) declarator
	       declarationList_opt compoundStatement contract
	      )
    | declarationSpecifiers
	  declarator
	  contract
	  declarationList_opt
	  compoundStatement
	  -> ^(FUNCTION_DEFINITION declarationSpecifiers declarator
	       declarationList_opt compoundStatement contract
	      )
	;


/* 6.9.1
 * Root: DECLARATION_LIST
 * Children: declaration (any number)
 */
declarationList_opt
	: declaration* -> ^(DECLARATION_LIST declaration*)
	;

/* An item in a CIVL-C contract.
 * 
 * Root: REQUIRES or ENSURES
 * Child: expression
 */
contractItem
	: separationLogicItem
    | porItem
	;

separationLogicItem
    :
      REQUIRES LCURLY expression RCURLY -> ^(REQUIRES expression RCURLY)
	| ENSURES LCURLY expression RCURLY -> ^(ENSURES expression RCURLY)

    ;
porItem
    :
      DEPENDS (LSQUARE expression RSQUARE)? LCURLY argumentExpressionList RCURLY -> ^(DEPENDS expression? argumentExpressionList)
    | GUARD (LSQUARE expression RSQUARE)? LCURLY argumentExpressionList RCURLY -> ^(GUARD expression? argumentExpressionList)
    | ASSIGNS (LSQUARE expression RSQUARE)? LCURLY argumentExpressionList RCURLY -> ^(ASSIGNS expression? argumentExpressionList)
    | READS (LSQUARE expression RSQUARE)? LCURLY argumentExpressionList RCURLY -> ^(READS expression? argumentExpressionList )
    ;

/* A CIVL-C contract: sequence of 0 or more
 * contract items.
 *
 * Root: CONTRACT
 * Children: 0 or more contractItem
 */
contract
	: contractItem* -> ^(CONTRACT contractItem*)
	;


/* A block item which can be called from the external world.
 * This requires a scope.
 */
blockItemWithScope
scope DeclarationScope;
@init {
  $DeclarationScope::isTypedef = false;
  $DeclarationScope::typedefNameUsed = false;
}
	: blockItem;

/* A block item: a declaration, function definition,
 * or statement.  Note that in C, a function definition
 * is not a block item, but in CIVL-C it is.
 */
blockItem
	:
	  (declarator contract
	   	  declarationList_opt LCURLY)=>
	  functionDefinition
    | (declarationSpecifiers declarator contract
	   	  declarationList_opt LCURLY)=>
	  functionDefinition
	| declaration	
	| pragma
    | statement
	;

/* 6.9
 * Root: TRANSLATION_UNIT
 * Children: blockItem
 *
 * Note that this accepts more than what C allows.
 * C only allows "external declarations".  This rule
 * allows any block item, and block items include
 * function definitions as well as statements,
 * declarations, etc.  These are permissible in the
 * CIVL-C language.  To enforce C's stricter restrictions,
 * do some checks on the tree after parsing completes.
 */
translationUnit
scope Symbols; // the global scope
scope DeclarationScope; // just to have an outermost one with isTypedef false
@init {
    $Symbols::types = new HashSet<String>();
    $Symbols::enumerationConstants = new HashSet<String>();
    $Symbols::isFunctionDefinition = false;
    $DeclarationScope::isTypedef = false;
    $DeclarationScope::typedefNameUsed = false;
}
	:	blockItem* EOF
		-> ^(TRANSLATION_UNIT blockItem*)
	;
