CIVL = civl
COMPARE = $(CIVL) compare
REPLAY = $(CIVL) replay

all: max

max: max.cvl max_seq.cvl max_par.cvl
	$(COMPARE) -inputB=4 -spec max.cvl max_seq.cvl \
	-impl -inputNPROCS=2 -inputBLOCK_SIZE=2 max.cvl max_par.cvl
	$(REPLAY) -spec max.cvl max_seq.cvl \
	-impl max.cvl max_par.cvl
	
clean: 
	rm -f *~
	rm -f -r CIVLREP
