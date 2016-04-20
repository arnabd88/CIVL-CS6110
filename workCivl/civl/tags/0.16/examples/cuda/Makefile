CIVL=civl
VERIFY=$(CIVL) verify

all: dot sum
	
dot: dot.cvl
	$(VERIFY) -inputN_BOUND=8 -inputTHREADS_PER_BLOCK=4 dot.cvl
	
sum: sum.cvl
	$(VERIFY) sum.cvl
