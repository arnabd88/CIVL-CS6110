CIVL = civl
VERIFY = $(CIVL) verify
COMPARE = $(CIVL) compare
REPLAY = $(CIVL) replay

all: mpiSerDot pthreadSerDot mpiThreadsDot hybridSerDot mpiHybridDot pthreadsHybridDot

mpiDot: mpithreads_mpi.c
	${VERIFY} -inputVECLEN=5 -input_mpi_nprocs=2 mpithreads_mpi.c

serDot: mpithreads_serial.c
	${VERIFY} -inputVECLEN=5 mpithreads_serial.c

pthreadDot: mpithreads_threads.c
	${VERIFY} -inputVECLEN=5 -inputMAXTHRDS=2 mpithreads_threads.c

hybridDot: mpithreads_both.c
	${VERIFY} -inputVECLEN=5 -inputMAXTHRDS=2 -input_mpi_nprocs=2 mpithreads_both.c

mpiSerDot: mpithreads_mpi.c mpithreads_serial.c
	${COMPARE} -inputVECLEN=5 -spec mpithreads_serial.c -impl -input_mpi_nprocs=2 mpithreads_mpi.c

pthreadSerDot: mpithreads_threads.c mpithreads_serial.c
	${COMPARE} -inputVECLEN=5 -spec mpithreads_serial.c -impl -inputMAXTHRDS=2 mpithreads_threads.c

mpiThreadsDot: mpithreads_mpi.c mpithreads_threads.c
	${COMPARE} -inputVECLEN=5 -spec -inputMAXTHRDS=2 mpithreads_threads.c -impl -input_mpi_nprocs=2 mpithreads_mpi.c

hybridSerDot: mpithreads_serial.c mpithreads_both.c
	${COMPARE} -inputVECLEN=5 -spec mpithreads_serial.c -impl -input_mpi_nprocs=2 -inputMAXTHRDS=2 mpithreads_both.c

mpiHybridDot: mpithreads_mpi.c mpithreads_both.c
	${COMPARE} -inputVECLEN=5 -input_mpi_nprocs=2 -spec mpithreads_mpi.c -impl -inputMAXTHRDS=2 mpithreads_both.c

pthreadsHybridDot: mpithreads_threads.c mpithreads_both.c
	${COMPARE} -inputVECLEN=5 -inputMAXTHRDS=2 -spec mpithreads_threads.c -impl -input_mpi_nprocs=2 mpithreads_both.c


clean: 
	rm -f -r CIVLREP
	rm -r -f *~
