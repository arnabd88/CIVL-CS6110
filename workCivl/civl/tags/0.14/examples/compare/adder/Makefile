CIVL = civl
COMPARE = $(CIVL) compare

all: adder

adder: adder_par.cvl adder_spec.cvl
	$(COMPARE) adder_par.cvl adder_spec.cvl -inputNPROCSB=2 -inputNB=4

adder: adder_par.cvl adder_spec.cvl
	$(COMPARE) -inputNB=4 -inputNPROCSB=2 -impl adder_par.cvl -spec adder_spec.cvl

clean: 
	rm -f *~
	rm -f -r CIVLREP