CIVL=civl
VERIFY=verify
COMPARE=compare

all: compare compare_adv spec par clean

compare: diffusion1d_spec.c diffusion1d_par.c
	$(CIVL) $(COMPARE) -inputNXB=3  -inputNSTEPS_BOUND=2 -inputwstep=1 -input_mpi_nprocs=2 \
	-spec diffusion1d_spec.c -impl diffusion1d_par.c

compare_adv: diffusion1d_spec.c diffusion1d_par.c
	$(CIVL) $(COMPARE) -inputNXB=5 -inputNSTEPS_BOUND=4 -inputwstep=1 \
	-input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=4 \
	-spec diffusion1d_spec.c -impl diffusion1d_par.c  

spec: diffusion1d_spec.c
	$(CIVL) $(VERIFY) -inputNXB=3 -inputNSTEPS_BOUND=2 -inputwstep=1 \
	diffusion1d_spec.c

par: diffusion1d_par.c
	$(CIVL) $(VERIFY) -inputNXB=3  -inputNSTEPS_BOUND=2 -inputwstep=1 \
	-input_mpi_nprocs=2 diffusion1d_par.c
clean: 
	rm -f *~
	rm -f -r CIVLREP