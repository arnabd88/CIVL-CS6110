CIVL=civl
VERIFY=$(CIVL) verify

all: mpi-pthreads
	
mpi-pthreads: mpi-pthreads.cvl
	$(VERIFY) -min mpi-pthreads.cvl
	$(CIVL) replay mpi-pthreads.cvl
