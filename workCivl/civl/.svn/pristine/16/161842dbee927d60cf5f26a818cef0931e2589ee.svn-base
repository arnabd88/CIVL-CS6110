#the cg3 cases are under developing, they keep running...

CIVL=civl
VERIFY=${CIVL} verify

all: cg2_cholesky cg2_sylvester cg2

cg2_cholesky: cg2_cholesky.cvl
	${VERIFY}  cg2_cholesky.cvl

cg2_sylvester: cg2_sylvester.cvl
	${VERIFY} cg2_sylvester.cvl

cg2: cg2.cvl
	${VERIFY} cg2.cvl

clean: 
	rm -f -r CIVLREP
	rm -r -f *~
