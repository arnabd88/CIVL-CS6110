CIVL=civl
VERIFY=$(CIVL) verify

all: mat-pie3 mat-pie100
	
mat-pie3: mpi-omp-pie-calculation.c
	$(VERIFY) -DMATH_ELABORATE_ASSUMPTIONS -input_NPROCS=2 -inputTHREAD_MAX=3 -ompLoopDecomp=ALL mpi-omp-pie-calculation.c
	
mat-pie100: mpi-omp-pie-calculation100.c
	$(VERIFY) -DMATH_ELABORATE_ASSUMPTIONS -input_NPROCS=2 -inputTHREAD_MAX=10 -ompLoopDecomp=ALL mpi-omp-pie-calculation100.c

clean: 
	rm -f -r CIVLREP
	rm -f *~
