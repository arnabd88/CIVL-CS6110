CIVL = civl
VERIFY = $(CIVL) verify
CC = cc

all: adder_par ring1 mpithreads_mpi mpi_pi_send mpi_prime

adder_par: adder_par.c
	$(VERIFY) -input__NPROCS=2 -inputNB=4 adder_par.c

ring1: ring1.c
	$(VERIFY) -input__NPROCS=5 ring1.c

mpithreads_mpi: mpithreads_mpi.c
	 $(VERIFY) -input__NPROCS=2 mpithreads_mpi.c

mpi_pi_send: mpi_pi_send.c
	$(VERIFY) -input__NPROCS=3 -enablePrintf=false mpi_pi_send.c

mpi_prime: mpi_prime.c
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false mpi_prime.c

mpi_gather: ${Gather_Scatter/mpi_gather.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_gather.c

mpi_scatter: ${Gather_Scatter/mpi_scatter.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_scatter.c

mpi_gatherv: ${Gather_Scatter/mpi_gatherv.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_gatherv.c

mpi_scatterv: ${Gather_Scatter/mpi_scatterv.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_scatterv.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~

