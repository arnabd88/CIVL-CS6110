CIVL=civl
VERIFY=verify
COMPARE=compare

all: compare

compare: diffusion1d_spec_revision.c diffusion1d_par_revision.c
	$(CIVL) $(COMPARE) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 -input__NPROCS=2 \
	-spec diffusion1d_spec_revision.c -impl diffusion1d_par_revision.c

compare_adv: diffusion1d_spec_revision.c diffusion1d_par_revision.c
	$(CIVL) $(COMPARE) -inputNX=5 -inputK=0.3 -inputNSTEPSB=4 -inputWSTEP=1 \
	-input__NPROCS_LOWER_BOUND=1 -input__NPROCS_UPPER_BOUND=4 \
	-spec diffusion1d_spec_revision.c -impl diffusion1d_par_revision.c  

spec: diffusion1d_spec_revision.c
	$(CIVL) $(VERIFY) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 \
	diffusion1d_spec_revision.c

par: diffusion1d_par_revision.c
	$(CIVL) $(VERIFY) -inputNX=3 -inputK=0.3 -inputNSTEPS=2 -inputWSTEP=1 \
	-input__NPROCS=2 diffusion1d_par_revision.c
clean: 
	rm -f *~
	rm -f -r CIVLREP