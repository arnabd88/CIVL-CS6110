CIVL=civl
VERIFY=$(CIVL) verify

all: diffusion1d ring
	
diffusion1d: diffusion1d.cvl
	$(VERIFY) -inputNPROCSB=3 -inputNSTEPSB=3 -inputNXB=6 -enablePrintf=false diffusion1d.cvl
	
ring: ring.cvl
	$(VERIFY) -inputNPROCS_BOUND=10 -inputN_BOUND=5 ring.cvl
