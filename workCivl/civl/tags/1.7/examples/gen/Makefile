CIVL=civl
VERIFY=${CIVL} verify 

all: gen simple simple2

gen: gen.c
	${VERIFY} gen.c

simple: simpleMPI.c
	${VERIFY} -input_mpi_nprocs=2 simpleMPI.c

simple2: simpleMPI2.c
	${VERIFY} -input_mpi_nprocs=2 simpleMPI2.c

clean:
	rm -rf CIVLREP
	rm -rf ~*
