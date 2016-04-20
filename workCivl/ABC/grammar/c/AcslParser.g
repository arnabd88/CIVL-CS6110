parser grammar AcslParser;

/*
 * Grammar for programming ACSL specification, 
 * with additional CIVL-C extensions.
 * Based on ACSL 1.9.
 * 
 * Author: Manchun Zheng, University of Delaware
 * Last changed: Jan 2016
 */

options
{
	language=Java;
	tokenVocab=AcslLexer;
	output=AST;
    backtrack=true;
}

tokens{
    ARGUMENT_LIST;
    BEHAVIOR_BODY;
    BEHAVIOR_COMPLETE;
    BEHAVIOR_DISJOINT;
    BINDER;
    BINDER_LIST;
    C_TYPE;
    CAST;
    CLAUSE_NORMAL;
    CLAUSE_BEHAVIOR;
    CLAUSE_COMPLETE;
    CONTRACT;
    EVENT_BASE;
    EVENT_PLUS;
    EVENT_SUB;
    EVENT_INTS;
    EVENT_LIST;
    EVENT_PARENTHESIZED;
    FUNC_CALL;
    FUNC_CONTRACT;
    FUNC_CONTRACT_BLOCK;
    ID_LIST;
    INDEX;
    LOGIC_TYPE;
    LOOP_ALLOC;
    LOOP_ASSIGNS;
    LOOP_BEHAVIOR;
    LOOP_CLAUSE;
    LOOP_CONTRACT;
    LOOP_CONTRACT_BLOCK;
    LOOP_FREE;
    LOOP_INVARIANT;
    LOOP_VARIANT;
    MPI_CONSTANT;
    MPI_EXPRESSION;
    OPERATOR;
    SET_BINDERS;
    SET_SIMPLE;
    SIZEOF_EXPR;
    SIZEOF_TYPE;
    TERM_PARENTHESIZED;
    TYPE_BUILTIN;
    TYPE_ID;
    VAR_ID;
    VAR_ID_BASE;
    VAR_ID_SQUARE;
    VAR_ID_STAR;
}

@header
{
package edu.udel.cis.vsl.abc.front.c.parse;
}

contract
    : function_contract
        -> ^(CONTRACT function_contract)
    | loop_contract
        -> ^(CONTRACT loop_contract)
    ;

loop_contract
    : LCOMMENT loop_contract_block RCOMMENT
        ->^(LOOP_CONTRACT loop_contract_block)
    ;

loop_contract_block
    : lc+=loop_clause* lb+=loop_behavior* lv=loop_variant?
        ->^(LOOP_CONTRACT_BLOCK $lc* $lb* $lv?)
    ;

loop_clause
    : loop_invariant SEMICOL
        ->^(LOOP_CLAUSE loop_invariant)
    | loop_assigns SEMICOL
        ->^(LOOP_CLAUSE loop_assigns)
    | loop_allocation SEMICOL
        ->^(LOOP_CLAUSE loop_allocation)
    ;

loop_invariant
    : LOOP INVARIANT term
        ->^(LOOP_INVARIANT term)
    ;

loop_assigns
    : LOOP ASSIGNS argumentExpressionList
        ->^(LOOP_ASSIGNS argumentExpressionList)
    ;

loop_allocation
    : LOOP ALLOC argumentExpressionList (COMMA term)?
        ->^(LOOP_ALLOC argumentExpressionList term?)
    | LOOP FREES argumentExpressionList
        ->^(LOOP_FREE argumentExpressionList)
    ;

loop_behavior
    : FOR ilist=id_list COLON lc+=loop_clause*
        ->^(LOOP_BEHAVIOR $ilist $lc*)
    ;

loop_variant
    : LOOP VARIANT term
        ->^(LOOP_VARIANT term)
    | LOOP VARIANT term FOR ID
        ->^(LOOP_VARIANT term ID)
    ;

/* sec. 2.3 Function contracts */
function_contract
    : LCOMMENT pure_function? full_contract_block RCOMMENT
      -> ^(FUNC_CONTRACT full_contract_block pure_function?)
    ;

pure_function
    : PURE SEMICOL
      ->^(PURE)
    ;

/* a full contract block non-terminal represents an ACSL contract
 * block for a function */
full_contract_block
    : (f+=function_clause)* (m+=contract_block)*
        (c+=completeness_clause_block)* 
        -> ^(FUNC_CONTRACT_BLOCK $f* $m* $c*) 
    ;

/* a partial contract block non-terminal represents an ACSL contract
 * block inside an MPI collective block. There is no nested MPI
 * collective block allowed */
partial_contract_block
    : (f+=function_clause)* (b+=named_behavior_block)* 
        (c+=completeness_clause_block)* 
        -> ^(FUNC_CONTRACT_BLOCK $f* $b* $c*) 
    ;

/* a block in contracts, either an mpi collective block or a behavior
* block. Behavior blocks are allowed to be inside an mpi collective
* block while an mpi collective block will not belong to a behavior
* block. An mpi collective block appears after a behavior block marks
* the end of the behavior block. */
contract_block
    : mpi_collective_block
    | named_behavior_block completeness_clause_block?
    ;

function_clause
    : requires_clause SEMICOL-> ^(CLAUSE_NORMAL requires_clause)
    | terminates_clause SEMICOL-> ^(CLAUSE_NORMAL terminates_clause)
    | simple_clause SEMICOL -> ^(CLAUSE_NORMAL simple_clause)
    ;

named_behavior_block
    : named_behavior -> ^(CLAUSE_BEHAVIOR named_behavior)
    ;

completeness_clause_block
    : completeness_clause SEMICOL -> ^(CLAUSE_COMPLETE completeness_clause)
    ;

requires_clause
    : REQUIRES term -> ^(REQUIRES term)
    ;

terminates_clause
    : TEMINATES term -> ^(TERMINATES term)
    ;

rel_op
    : EQ | NEQ | LTE | GTE | LT | GT
    ;

binders
    : binder (COMMA binder)*
        ->^(BINDER_LIST binder+)
    ;

binder
    : type_expr variable_ident (COMMA variable_ident)*
        ->^(BINDER type_expr variable_ident+)
    ;

type_expr
    : logic_type_expr ->^(LOGIC_TYPE logic_type_expr)
    | c_type ->^(C_TYPE c_type)
    ;

logic_type_expr
    : built_in_logic_type ->^(TYPE_BUILTIN built_in_logic_type)
    | ID ->^(TYPE_ID ID)
    ;

c_type
    : CHAR | DOUBLE | FLOAT | INT | LONG | SHORT | VOID
    ;

built_in_logic_type
    : BOOLEAN | INTEGER | REAL
    ;

variable_ident
    : STAR variable_ident_base
        ->^(VAR_ID_STAR variable_ident_base)
    | variable_ident_base LSQUARE RSQUARE
        ->^(VAR_ID_SQUARE variable_ident_base)
    | variable_ident_base
        ->^(VAR_ID variable_ident_base)
    ;

variable_ident_base
    : ID
      ->^(ID)
    | LPAREN variable_ident RPAREN
      ->^(VAR_ID_BASE variable_ident)
    ;

guards_clause
    : GUARDS term ->^(GUARDS term)
    ;

simple_clause
    : assigns_clause
    | ensures_clause 
    | allocation_clause
    | reads_clause
    | depends_clause
    | guards_clause
    ;

assigns_clause
    : ASSIGNS argumentExpressionList ->^(ASSIGNS argumentExpressionList)
    ;

ensures_clause
    : ENSURES term ->^(ENSURES term)
    ;

allocation_clause
    : ALLOC argumentExpressionList (COMMA term)? ->^(ALLOC argumentExpressionList term?)
    | FREES argumentExpressionList ->^(FREES argumentExpressionList)
    ;

reads_clause
    : READS argumentExpressionList ->^(READS argumentExpressionList)
    ;
/*
reaches_clause
    : REACHES argumentExpressionList ->^(REACHES argumentExpressionList)
    ;
*/
depends_clause
    : DEPENDS event_list ->^(DEPENDS event_list)
    ;

event_list
    : event (COMMA event)* -> ^(EVENT_LIST event+)
    ;

event
    : event_base PLUS event_base
        -> ^(EVENT_PLUS event_base event_base)
    | event_base SUB event_base
        -> ^(EVENT_SUB event_base event_base)
    | event_base AMPERSAND event_base
        -> ^(EVENT_INTS event_base event_base)
    | event_base
        -> ^(EVENT_BASE event_base)
    ;

event_base
    : READ LPAREN argumentExpressionList RPAREN
        -> ^(READ argumentExpressionList)
    | WRITE LPAREN argumentExpressionList RPAREN
        -> ^(WRITE argumentExpressionList)
    | REACH LPAREN argumentExpressionList RPAREN
        -> ^(REACH argumentExpressionList)
    | CALL LPAREN ID (COMMA argumentExpressionList)? RPAREN
        -> ^(CALL ID argumentExpressionList?)
    | NOACT
        -> ^(NOACT)
    | ANYACT
        -> ^(ANYACT)
    | LPAREN event RPAREN
        -> ^(EVENT_PARENTHESIZED event)
    ;

/* ACSL-MPI extensions: constructors */
mpi_collective_block
    : MPI_COLLECTIVE LPAREN ID COMMA kind=mpi_collective_kind  RPAREN COLON
      c=partial_contract_block -> ^(MPI_COLLECTIVE ID $kind $c)
    ;



/* sec. 2.3.3 contracts with named behaviors */
named_behavior
    : BEHAVIOR ID COLON behavior_body ->^(BEHAVIOR ID behavior_body)
    ;

behavior_body
    : (b+=behavior_clause SEMICOL)+ -> ^(BEHAVIOR_BODY $b+)
    ;

behavior_clause
    : assumes_clause 
    | requires_clause
    | simple_clause
    ;

assumes_clause
    : ASSUMES term ->^(ASSUMES term)
    ;

completeness_clause
    : COMPLETE BEHAVIORS id_list ->^(BEHAVIOR_COMPLETE id_list)
    | DISJOINT BEHAVIORS id_list ->^(BEHAVIOR_DISJOINT id_list)
    ;

id_list
    :
    | ID (COMMA ID)* ->^(ID_LIST ID+)
    ;

/* 6.5.1 */
primaryExpression
	: constant
    | ID
	| STRING_LITERAL
    | LCURLY term BAR binders (SEMICOL term)? RCURLY
        ->^(SET_BINDERS term binders term?)
    | LCURLY term RCURLY
        ->^(SET_SIMPLE term)
	| LPAREN term RPAREN 
	  -> ^(TERM_PARENTHESIZED term)
    | mpi_expression -> ^(MPI_EXPRESSION mpi_expression)
    | REMOTE_ACCESS LPAREN a=ID COMMA b=primaryExpression RPAREN
      -> ^(REMOTE_ACCESS $a $b)
	;

/* 6.5.2 */
postfixExpression
	: (primaryExpression -> primaryExpression)
		// array index operator:
	  ( l=LSQUARE term RSQUARE
	    -> ^(OPERATOR
	           INDEX[$l]
	           ^(ARGUMENT_LIST $postfixExpression term)
	           RSQUARE)
	  |	// function call:
	    LPAREN argumentExpressionList RPAREN
	    -> ^(FUNC_CALL $postfixExpression argumentExpressionList
	    	 )
	  | DOT ID
	    -> ^(DOT $postfixExpression ID)
	  | ARROW ID
	    -> ^(ARROW $postfixExpression ID)
	  )*
	;

/* 6.5.2 */
argumentExpressionList
	: -> ^(ARGUMENT_LIST)
	| assignmentExpression (COMMA assignmentExpression)*
	  -> ^(ARGUMENT_LIST assignmentExpression+)
	;

/* 6.5.3 */
unaryExpression
	: postfixExpression
	| unary_op castExpression
	  -> ^(OPERATOR unary_op ^(ARGUMENT_LIST castExpression))
	| (SIZEOF LPAREN type_expr)=> SIZEOF LPAREN type_expr RPAREN
	  -> ^(SIZEOF_TYPE type_expr)
	| SIZEOF unaryExpression
	  -> ^(SIZEOF_EXPR unaryExpression)
	//| spawnExpression
    | UNION LPAREN argumentExpressionList RPAREN
        -> ^(UNION argumentExpressionList)
    | INTER LPAREN argumentExpressionList RPAREN
        -> ^(INTER argumentExpressionList)
    | VALID LPAREN term RPAREN
        -> ^(VALID term)
	;
    
    

/* CIVL $spawn expression */
//spawnExpression
//	: SPAWN postfixExpressionRoot LPAREN 
	 // argumentExpressionList RPAREN 
	 // -> ^(SPAWN LPAREN postfixExpressionRoot ABSENT
	   //    argumentExpressionList RPAREN)
	//;

/* 6.5.4 */
// ambiguity 1: (expr) is a unary expression and looks like (typeName).
// ambiguity 2: (typeName){...} is a compound literal and looks like cast
castExpression
	: (LPAREN type_expr RPAREN)=> l=LPAREN type_expr RPAREN castExpression
	  -> ^(CAST type_expr castExpression)
	| unaryExpression
	;

remoteExpression
	:(castExpression -> castExpression)
	( HASH y=castExpression
	  -> ^(OPERATOR HASH ^(ARGUMENT_LIST $remoteExpression $y))
    )*
	;

/* 6.5.5 */
multiplicativeExpression
	: (remoteExpression -> remoteExpression)
	( STAR y=remoteExpression
	  -> ^(OPERATOR STAR ^(ARGUMENT_LIST $multiplicativeExpression $y))
	| DIVIDE y=remoteExpression
	  -> ^(OPERATOR DIVIDE ^(ARGUMENT_LIST $multiplicativeExpression $y))
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
	: EQ | NEQ
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
	  ( BAR y=exclusiveOrExpression
	    -> ^(OPERATOR BAR ^(ARGUMENT_LIST $inclusiveOrExpression $y))
	  )*
	;

/* 6.5.13 */
logicalAndExpression
	: ( inclusiveOrExpression -> inclusiveOrExpression )
	  ( LAND y=inclusiveOrExpression
	    -> ^(OPERATOR LAND ^(ARGUMENT_LIST $logicalAndExpression $y))
	  )*
	;

/* 6.5.14 */
logicalOrExpression
	: ( logicalAndExpression -> logicalAndExpression )
	  ( LOR y=logicalAndExpression
	    -> ^(OPERATOR LOR ^(ARGUMENT_LIST $logicalOrExpression $y))
	  )*
	;
	
/* Added for CIVL-C.  Usually 6.5.15 would use logicalOrExpression. */
logicalImpliesExpression
	: ( logicalOrExpression -> logicalOrExpression )
	  ( IMPLY y=logicalOrExpression
	    -> ^(OPERATOR IMPLY ^(ARGUMENT_LIST $logicalImpliesExpression $y))
	  )*
    	;

/* 6.5.15 */
conditionalExpression
	: logicalImpliesExpression
	( -> logicalImpliesExpression
    	| QUESTION term COLON conditionalExpression
    	  -> ^(OPERATOR QUESTION
    	       ^(ARGUMENT_LIST
    	         logicalImpliesExpression
    	         term
    	         conditionalExpression))
    	)
	;

/* A CIVL-C quantified expression using $exists or $forall.
 */
quantifierExpression
	: quantifier binders SEMICOL assignmentExpression
	  -> ^(quantifier binders assignmentExpression)
	//| quantifier LCURLY id=IDENTIFIER ASSIGN
	  //lower=additiveExpression DOTDOT upper=additiveExpression
	  //RCURLY cond=assignmentExpression
	  //-> ^(quantifier $id $lower $upper $cond)
// eventually change to the following:
//	| quantifier LCURLY id=IDENTIFIER ASSIGN rangeExpression
//	  RCURLY cond=assignmentExpression
//	  -> ^(quantifier $id rangeExpression $cond)
	;

/* One of the CIVL-C first-order quantifiers.
 * UNIFORM represents uniform continuity.  
 */	
quantifier
	: FORALL | EXISTS
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
	: (unaryExpression ASSIGN)=>
	  unaryExpression ASSIGN assignmentExpression
	  -> ^(OPERATOR ASSIGN
	       ^(ARGUMENT_LIST unaryExpression assignmentExpression))
	| conditionalExpression
	| quantifierExpression
	;

/* 6.5.17
 * assignmentExpression or
 * Root: OPERATOR
 * Child 0: COMMA
 * Child 1: ARGUMENT_LIST
 * Child 1.0: arg0
 * Child 1.1: arg1
 */
term
	: assignmentExpression
    ;
			
/* 6.6 */
constantExpression
	: conditionalExpression 
	;

constant
	: INTEGER_CONSTANT
	| FLOATING_CONSTANT
	| CHARACTER_CONSTANT
	| TRUE | FALSE | RESULT | NOTHING | ELLIPSIS
    | SELF | NULL
    | mpi_constant -> ^(MPI_CONSTANT mpi_constant)
	;

/* ACSL-MPI extensions Expressions and Constants  */
mpi_expression
    : MPI_EMPTY_IN LPAREN primaryExpression RPAREN
      -> ^(MPI_EMPTY_IN primaryExpression)
    | MPI_EMPTY_OUT LPAREN primaryExpression RPAREN
      -> ^(MPI_EMPTY_OUT primaryExpression)
    | MPI_AGREE LPAREN a=variable_ident_base RPAREN /* seems variable_ident not ready yet */
      -> ^(MPI_AGREE $a) 
    | MPI_REGION LPAREN a=primaryExpression COMMA b=primaryExpression COMMA c=primaryExpression RPAREN
      -> ^(MPI_REGION $a $b $c)
    | MPI_EQUALS LPAREN a=primaryExpression COMMA b=primaryExpression COMMA c=primaryExpression COMMA d=primaryExpression RPAREN
      -> ^(MPI_EQUALS $a $b $c $d)
    ;

mpi_constant
    : MPI_COMM_RANK | MPI_COMM_SIZE
    ;

mpi_collective_kind
    : COL | P2P | BOTH
    ;

unary_op
    : PLUS | MINUS | NOT | COMP | STAR | AMPERSAND
    ;

binary_op
    : PLUS | MINUS | STAR | DIVIDE | MOD | LSHIFT | RSHIFT
    | EQ | NEQ | LTE | GTE | LT | GT
    | LAND | LOR | XOR | AMPERSAND | BAR | IMPLY | EQUIV | BITXOR
    ;



