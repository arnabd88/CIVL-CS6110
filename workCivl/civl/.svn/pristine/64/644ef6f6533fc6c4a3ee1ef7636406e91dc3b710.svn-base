
CIVL = civl
VERIFY = $(CIVL) verify
CC = cc

all: mpi_wave1d mpi_diff2d mpi_diff1d mpi_pi mpi_gather mpi_scatter mpi_gatherv mpi_scatterv mpi_reduce mpi_sysStatus mpi_sysStatusBad mpi_sysStatusBad2 mpi_prime mpi_matmat sum_array

mpi_wave1d: wave1d.c
	$(VERIFY) wave1d.c

mpi_diff2d: diffusion2d.c
	$(VERIFY) -inputNPROCSX=2 -inputNPROCSY=2 -inputNSTEPSB=3 diffusion2d.c

mpi_diff1d: diffusion1d.c
	$(VERIFY)  diffusion1d.c

mpi_pi: mpi_pi.c
	$(VERIFY) mpi_pi.c

mpi_gather: ${routines/Gather_Scatter/mpi_gather.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_gather.c

mpi_scatter: ${routines/Gather_Scatter/mpi_scatter.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_scatter.c

mpi_gatherv: ${routines/Gather_Scatter/mpi_gatherv.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_gatherv.c

mpi_scatterv: ${routines/Gather_Scatter/mpi_scatterv.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_scatterv.c

mpi_scatter_inplace: ${routines/Gather_Scatter/mpi_scatter_inPlace.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_scatter_inPlace.c

mpi_gather_inplace: ${routines/Gather_Scatter/mpi_gather_inPlace.c}
	$(VERIFY) -input_mpi_nprocs=4 -enablePrintf=false routines/Gather_Scatter/mpi_gather_inPlace.c

mpi_sysStatus: ${routines//mpiSysStatus.c}
	$(VERIFY) routines/mpiSysStatus.c

mpi_sysStatusBad: ${routines/mpiSysStatusBad.c}
	$(VERIFY) routines/mpiSysStatusBad.c

mpi_sysStatusBad2: ${routines/mpiSysStatusBad2.c}
	$(VERIFY) routines/mpiSysStatusBad2.c

mpi_probe: ${routines/probe.c}
	$(VERIFY) routines/probe.c

mpi_reduce: ${routines/reduce.c}
	$(VERIFY) routines/reduce.c

mpi_prime: mpi_prime.c
	$(VERIFY) mpi_prime.c

mpi_matmat: ${matmat_mw/matmat_mw.c}
	$(VERIFY) matmat_mw/matmat_mw.c

mpi_sum_array: sum_array.c
	$(VERIFY) sum_array.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~

