CIVL = civl
VERIFY = $(CIVL) verify
CC = cc

all: adder_par ring1 mpithreads_mpi mpi_pi_send mpi_prime

adder_par: adder_par.c
	$(VERIFY) -input__NPROCS=2 adder_par.c -inputNB=4

ring1: ring1.c
	$(VERIFY) -input__NPROCS=5 ring1.c

mpithreads_mpi: mpithreads_mpi.c
	 $(VERIFY) -input__NPROCS=2 mpithreads_mpi.c

mpi_pi_send: mpi_pi_send.c
	$(VERIFY) -input__NPROCS=3 -enablePrintf=false mpi_pi_send.c

mpi_prime: mpi_prime.c
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false mpi_prime.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~

