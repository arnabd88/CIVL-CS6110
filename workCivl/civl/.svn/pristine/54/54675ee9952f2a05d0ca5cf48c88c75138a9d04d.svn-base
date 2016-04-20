CIVL = civl
COMPARE = $(CIVL) compare

all: adder

adder: adder_par.cvl adder_spec.cvl
	$(COMPARE) adder_par.cvl adder_spec.cvl -inputNPROCSB=2 -inputNB=4

clean: 
	rm -f *~
	rm -f -r CIVLREP