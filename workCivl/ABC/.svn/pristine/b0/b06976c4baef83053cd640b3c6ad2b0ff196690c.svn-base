grammar g1;
options { output=AST; }
tokens { B_CHAIN; }
//r	:	(A | (b_chain A))* b_chain?;
r	:	(A | b_chain)*;

//b_chain	:	B+ -> ^(B_CHAIN B+);
b_chain	:	(options {greedy=true;} : B)+ -> ^(B_CHAIN B+);

A 	:	'A';
B	:	'B';

// BB should yield ^(BCHAIN B B)