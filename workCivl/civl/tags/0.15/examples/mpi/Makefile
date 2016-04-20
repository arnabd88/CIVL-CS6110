
CIVL = civl
VERIFY = $(CIVL) verify
CC = cc

all: adder_par ring1 mpithreads_mpi mpi_pi_send mpi_prime

adder_par: adder_par.c
	$(VERIFY) -input__NPROCS=2 -inputNB=4 adder_par.c

ring1: ring1.c
	$(VERIFY) -input__NPROCS=5 ring1.c

mpi_prime: mpi_prime.c
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false mpi_prime.c

mpi_wave1d: wave1d.c
	$(VERIFY) wave1d.c

mpi_diff2d: diffusion2d.c
	$(VERIFY) -inputNPROCSX=2 -inputNPROCSY=2 -inputNSTEPSB=3 diffusion2d.c

mpi_pi: mpi_pi.c
	$(VERIFY) mpi_pi.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~

