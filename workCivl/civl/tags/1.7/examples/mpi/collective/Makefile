CIVL = civl
VERIFY = $(CIVL) verify
REPLAY = $(CIVL) replay

all: bcast_bad scatter_bad gather_bad scatterGather scatterGather_bad scatterAllgather vectorSum

bcast_bad: bcast_bad.c
	${VERIFY} -input_mpi_nprocs=6 bcast_bad.c

scatter_bad: scatter_bad.c
	${VERIFY} -input_mpi_nprocs=5 scatter_bad.c

gather_bad: gather_bad.c
	${VERIFY} -input_mpi_nprocs=5 gather_bad.c

scatterGather: scatterGather.c
	${VERIFY} -input_mpi_nprocs=5 scatterGather.c

scatterGather_bad: scatterGather_bad.c
	${VERIFY} -input_mpi_nprocs=5 scatterGather_bad.c
	${REPLAY}  scatterGather_bad.c

BcastReduce:  BcastReduce.c BcastReduce2.c
	$(VERIFY) -input_mpi_nprocs_hi=8 -input_mpi_nprocs_lo=1 BcastReduce.c
	$(VERIFY) -input_mpi_nprocs_hi=8 -input_mpi_nprocs_lo=1 BcastReduce2.c

scatterAllgather: scatterAllgather.c
	${VERIFY} -input_mpi_nprocs=5 scatterAllgather.c

scatterAllgather_bad: scatterAllgather_bad.c
	${VERIFY} -input_mpi_nprocs=5 scatterAllgather_bad.c

vectorSum: vectorSum.c
	${VERIFY} -input_mpi_nprocs=5 vectorSum.c
	
vectorSum_bad: vectorSum_bad.c
	${VERIFY} -input_mpi_nprocs=5 vectorSum_bad.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~
