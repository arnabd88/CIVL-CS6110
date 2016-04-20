CIVL=civl
VERIFY=$(CIVL) verify

all: ring ring2

ring: ring.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -inputNPROCS=3 ring.cvl -simplify=false

ring2: ring2.cvl mp_root2.cvh mp_proc2.cvh
	$(VERIFY) -inputNPROCS=3 ring2.cvl -simplify=false

diffusion1d: diffusion1d.cvl
	$(VERIFY) -inputNPROCSB=3 -inputNSTEPSB=3 -inputWSTEP=1 \
          -inputNXB=6 diffusion1d.cvl

