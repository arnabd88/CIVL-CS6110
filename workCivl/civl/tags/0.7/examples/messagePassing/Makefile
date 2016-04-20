CIVL=civl
VERIFY=$(CIVL) verify

all: ring ring2

ring: ring.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -inputNPROCS=3 ring.cvl -simplify=false
	
ring2: ring2.cvl mp_root2.cvh mp_proc2.cvh
	$(VERIFY) -inputNPROCS=3 ring2.cvl -simplify=false

