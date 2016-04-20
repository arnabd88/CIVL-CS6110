CIVL=civl
VERIFY=$(CIVL) verify

all: dot sum
	
dot: dot.cvl
	$(VERIFY) dot.cvl -inputN_BOUND=8 -inputTHREADS_PER_BLOCK=4
	
sum: sum.cvl
	$(VERIFY) sum.cvl
