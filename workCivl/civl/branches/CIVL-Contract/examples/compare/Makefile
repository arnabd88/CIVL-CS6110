CIVL = civl
COMPARE = $(CIVL) compare
ADDER_PATH = ./adder/
DIFFUSION_PATH = ./diffusion1d/
MAX_PATH = ./max/

all: sumN adder diffusion1d max

sumN: sumNimpl.cvl sumNspec.cvl
	$(COMPARE) -inputN=10 -spec sumNspec.cvl -impl sumNimpl.cvl

adder: $(ADDER_PATH)adder_par.cvl $(ADDER_PATH)adder_spec.cvl
	$(COMPARE) -inputNB=4 -inputNPROCSB=2 -impl $(ADDER_PATH)adder_par.cvl \
	-spec $(ADDER_PATH)adder_spec.cvl

diffusion1d: $(DIFFUSION_PATH)diffusion1d_spec_revision.c $(DIFFUSION_PATH)diffusion1d_par_revision.c
	$(COMPARE) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 -input_mpi_nprocs=2 \
	-spec $(DIFFUSION_PATH)diffusion1d_spec_revision.c \
	-impl $(DIFFUSION_PATH)diffusion1d_par_revision.c

max: $(MAX_PATH)max.cvl $(MAX_PATH)max_seq.cvl $(MAX_PATH)max_par.cvl
	$(COMPARE) -inputB=4 -spec $(MAX_PATH)max.cvl $(MAX_PATH)max_seq.cvl \
	-impl -inputNPROCS=2 -inputBLOCK_SIZE=2 $(MAX_PATH)max.cvl $(MAX_PATH)max_par.cvl
	
clean: 
	rm -f *~
	rm -f -r CIVLREP
