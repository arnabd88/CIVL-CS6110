parser grammar OmpParser;

options
{
	language=Java;
	tokenVocab=OmpLexer;
	output=AST;
}

import CivlCParser;

tokens
{
	IDENTIFIER_LIST;	
	PARALLEL_FOR;
	PARALLEL_SECTIONS;
	UNIQUE_FOR;
	UNIQUE_PARALLEL;
	DATA_CLAUSE;
	FOR_CLAUSE;
}

/* ANTLR 3.5 doesn't allow redefinition of headers in composite grammars.
Our solution for this is: add the header (package, imported package)
to the generated java file in ant.
@header
{
package edu.udel.cis.vsl.abc.parse.common;
}*/

@members {
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
}

// openMP grammar :  a bit old
//  missing some things, e.g., collapse, block, ...
  
openmp_construct
  : 
    parallel_for_directive
  | parallel_sections_directive
  | parallel_directive
  | for_directive
  | sections_directive
  | single_directive
  | master_directive
  | critical_directive
  | ordered_directive
  | section_directive
  | ompatomic_directive
  | barrier_directive
  | flush_directive
  | threadprivate_directive
  ;

parallel_directive
  : PARALLEL  (p+=parallel_clause)*
  -> ^(PARALLEL $p*)
  ;

parallel_clause
  : unique_parallel_clause
  | data_clause
  ;
  
master_directive
  : MASTER -> ^(MASTER)
  ;

critical_directive
  : CRITICAL  (LPAREN  id=IDENTIFIER  RPAREN)?
  -> ^(CRITICAL $id?)
  ;
  
sections_directive
  : SECTIONS  (s+=sections_clause)*
  -> ^(SECTIONS $s*)
  ;

sections_clause
  : data_clause
  | nowait_directive
  ;

section_directive
  : SECTION -> ^(SECTION)
  ;
  
parallel_for_directive
  : PARALLEL FOR p+=parallel_for_clause*
    -> ^(PARALLEL_FOR $p*)
  ;

parallel_for_clause
  : unique_parallel_clause
  | unique_for_clause
  | data_clause
  ;

parallel_sections_directive
  : PARALLEL  SECTIONS  p+=parallel_sections_clause*
    -> ^(PARALLEL_SECTIONS $p*)
  ;

parallel_sections_clause
  : unique_parallel_clause
  | data_clause
  ;

single_directive
  : SINGLE  s+=single_clause*
    -> ^(SINGLE $s*)
  ;

single_clause
  : data_clause
  | nowait_directive
  ;

barrier_directive
  : BARRIER -> ^(BARRIER)
  ;
  
ompatomic_directive
  : OMPATOMIC c0=atomic_clasue? c1=seq_cst_clause? 
    -> ^(OMPATOMIC $c0? $c1?)
  ;
  
atomic_clasue
	: READ | WRITE | UPDATE | CAPTURE	
	;
	
seq_cst_clause
	: SEQ_CST	
	;

flush_directive
  : FLUSH  f=flush_vars?
    -> ^(FLUSH $f?)
  ;

flush_vars
  : LPAREN   i=identifier_list  RPAREN
    -> ^(IDENTIFIER_LIST $i)
  ;

ordered_directive
  : ORDERED -> ^(ORDERED)
  ;
  
nowait_directive
  : NOWAIT -> ^(NOWAIT)
  ;

threadprivate_directive
  : THD_PRIVATE  LPAREN  i=identifier_list  RPAREN
    -> ^(THD_PRIVATE $i)
  ;

for_directive
  : FOR  (f+=for_clause)*
    -> ^(FOR $f*)
  ;

for_clause
  : u=unique_for_clause -> ^(FOR_CLAUSE $u)
  | d=data_clause -> ^(FOR_CLAUSE $d)
  | n=nowait_directive -> ^(FOR_CLAUSE $n)
  ;

unique_for_clause
  : ORDERED ->^(UNIQUE_FOR ORDERED)
  | s1=schedule_clause -> ^(UNIQUE_FOR $s1)
  | c=collapse_clause -> ^(UNIQUE_FOR $c)
  ;
  
schedule_clause
	: SCHEDULE  LPAREN  s1=schedule_kind  COMMA  e=expression  RPAREN
      -> ^(SCHEDULE $s1 $e)
    |  SCHEDULE  LPAREN  s=schedule_kind  RPAREN
	  -> ^(SCHEDULE $s)
	;
	
collapse_clause
	:
	COLLAPSE  LPAREN  i=INTEGER_CONSTANT  RPAREN
    -> ^(COLLAPSE $i)
	;

schedule_kind
  : STATIC -> ^(STATIC)
  | DYNAMIC -> ^(DYNAMIC)
  | GUIDED -> ^(GUIDED)
  | RUNTIME -> ^(RUNTIME)
  ;

unique_parallel_clause
  : i=if_clause 
    -> ^(UNIQUE_PARALLEL $i)
  | n=num_threads_clause 
    -> ^(UNIQUE_PARALLEL $n)
  ;
  
if_clause
  : IF  LPAREN  e1=expression  RPAREN
    -> ^(IF $e1)
  ;
  
num_threads_clause
  : NUM_THREADS  LPAREN  e2=expression  RPAREN
    -> ^(NUM_THREADS $e2)
  ;

data_clause
  : d1=private_clause
    -> ^(DATA_CLAUSE $d1)
  | d2=firstprivate_clause
    -> ^(DATA_CLAUSE $d2)
  | d3=lastprivate_clause
    -> ^(DATA_CLAUSE $d3)
  | d4=shared_clause
    -> ^(DATA_CLAUSE $d4)
  | d5=default_clause
    -> ^(DATA_CLAUSE $d5)
  | d6=reduction_clause
    -> ^(DATA_CLAUSE $d6)
  | d7=copyin_clause
    -> ^(DATA_CLAUSE $d7)
  | d8=copyprivate_clause
    -> ^(DATA_CLAUSE $d8)
  ;
  
private_clause
  : PRIVATE  LPAREN  i1=identifier_list  RPAREN 
    -> ^(PRIVATE $i1)
  ;
  
firstprivate_clause
  : FST_PRIVATE  LPAREN  i2=identifier_list  RPAREN
    -> ^(FST_PRIVATE $i2)
  ;
  
lastprivate_clause
  : LST_PRIVATE  LPAREN  i3=identifier_list  RPAREN
    -> ^(LST_PRIVATE $i3)
  ;
  
shared_clause
  : SHARED  LPAREN  i4=identifier_list  RPAREN
    -> ^(SHARED $i4)
  ;
  
default_clause
  : DEFAULT  LPAREN  SHARED  RPAREN
    -> ^(DEFAULT SHARED)
  | DEFAULT  LPAREN  NONE  RPAREN
    -> ^(DEFAULT NONE)
  ;
  
reduction_clause
  : REDUCTION LPAREN r=reduction_operator COLON i5=identifier_list RPAREN
    -> ^(REDUCTION $r $i5)
  ;
  
copyin_clause
  : COPYIN  LPAREN  i6=identifier_list  RPAREN
    -> ^(COPYIN $i6)
  ;
  
copyprivate_clause
  : COPYPRIVATE  LPAREN  i7=identifier_list  RPAREN
    -> ^(COPYPRIVATE $i7)
  ;

reduction_operator
  : PLUS -> ^(PLUS)
  | STAR -> ^(STAR)
  | SUB -> ^(SUB)
  | AMPERSAND -> ^(AMPERSAND)
  | BITXOR -> ^(BITXOR)
  | BITOR -> ^(BITOR)
  | AND -> ^(AND)
  | OR -> ^(OR)
  | IDENTIFIER -> ^(IDENTIFIER)
  ;

identifier_list
  :
  i1=IDENTIFIER ( COMMA  i2+=IDENTIFIER)* 
  -> ^(IDENTIFIER_LIST $i1 $i2*)
  ;
  
