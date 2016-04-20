CIVL=civl
VERIFY=verify
COMPARE=compare

all: compare

compare: diffusion1d_spec.c diffusion1d_par.c
	$(CIVL) $(COMPARE) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 -input__mpi_nprocs=2 \
	-spec diffusion1d_spec.c -impl diffusion1d_par.c

compare_adv: diffusion1d_spec.c diffusion1d_par.c
	$(CIVL) $(COMPARE) -inputNX=5 -inputK=0.3 -inputNSTEPSB=4 -inputWSTEP=1 \
	-input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=4 \
	-spec diffusion1d_spec.c -impl diffusion1d_par.c  

spec: diffusion1d_spec.c
	$(CIVL) $(VERIFY) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 \
	diffusion1d_spec.c

par: diffusion1d_par.c
	$(CIVL) $(VERIFY) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 \
	-input__mpi_nprocs=2 diffusion1d_par.c
clean: 
	rm -f *~
	rm -f -r CIVLREP