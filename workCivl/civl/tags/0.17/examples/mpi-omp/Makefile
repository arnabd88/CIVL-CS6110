CIVL=civl
VERIFY=$(CIVL) verify

all: mat-infnorm
	
mat-infnorm: mpi-omp-mat-infnorm-blkstp.c
	$(VERIFY) -input_NPROCS=2 -inputTHREAD_MAX=2 -ompNoSimplify mpi-omp-mat-infnorm-blkstp.c
