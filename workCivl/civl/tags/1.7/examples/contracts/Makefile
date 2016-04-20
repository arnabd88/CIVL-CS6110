VERIFY=civl verify -input_mpi_nprocs=3 -deadlock=potential -mpiContract 

all: $(patsubst  %.c, C_%, $(wildcard *.c)) $(patsubst  %.cvl, CVL_%, $(wildcard *.cvl))

C_%: %.c
	$(VERIFY) $<

CVL_%: %.cvl
	$(VERIFY) $<

clean: 
	rm -r -f CIVLREP *~