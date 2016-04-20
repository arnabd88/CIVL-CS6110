CIVL = civl
VERIFY = $(CIVL) verify
CC = cc

all: mpi_gather mpi_scatter mpi_gatherv mpi_scatterv

mpi_gather: ${Gather_Scatter/mpi_gather.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_gather.c

mpi_scatter: ${Gather_Scatter/mpi_scatter.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_scatter.c

mpi_gatherv: ${Gather_Scatter/mpi_gatherv.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_gatherv.c

mpi_scatterv: ${Gather_Scatter/mpi_scatterv.c}
	$(VERIFY) -input__NPROCS=4 -enablePrintf=false Gather_Scatter/mpi_scatterv.c

mpi_sysStatus: mpiSysStatus.c
	$(VERIFY) mpiSysStatus.c

mpi_sysStatusBad: mpiSysStatusBad.c
	$(VERIFY) mpiSysStatusBad.c

mpi_sysStatusBad2: mpiSysStatusBad2.c
	$(VERIFY) mpiSysStatusBad2.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~

