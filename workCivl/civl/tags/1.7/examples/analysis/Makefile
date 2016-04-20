CIVL=civl
VERIFY=${CIVL} verify

all: max abs abs2

max: unreached.c
	${VERIFY} -showUnreached unreached.c

abs: abs.c
	${VERIFY} -analyze_abs abs.c

abs2: abs2.c
	${VERIFY} -analyze_abs abs2.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~
