CIVL=civl
VERIFY=$(CIVL) verify

all: ring ring2 ring3 diffusion1d

ring: ring.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -inputNPROCS_BOUND=10 -inputN_BOUND=5 ring.cvl

ring2: ring2.cvl mp_root2.cvh mp_proc2.cvh
	$(VERIFY) -inputNPROCS=3 -simplify=false ring2.cvl

ring3: ring3.cvl
	$(VERIFY) ring3.cvl

diffusion1d: diffusion1d.cvl
	$(VERIFY) -inputNPROCSB=3 -inputNSTEPSB=3 -inputWSTEP=1 \
          -inputNXB=6 diffusion1d.cvl

