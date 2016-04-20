CIVL = civl
COMPARE = $(CIVL) compare
ADDER_PATH = ./adder/

all: sumN adder_comp

sumN: sumNimpl.cvl sumNspec.cvl
	$(COMPARE) sumNspec.cvl sumNimpl.cvl -inputN=10

adder_comp: $(ADDER_PATH)adder_par.cvl $(ADDER_PATH)adder_spec.cvl
	$(COMPARE) $(ADDER_PATH)adder_par.cvl $(ADDER_PATH)adder_spec.cvl -inputNB=4 -inputNPROCSB=2

clean: 
	rm -f *~
	rm -f -r CIVLREP