CIVL = civl
COMPARE = $(CIVL) compare

all: sum

sum: sumNimpl.cvl sumNspec.cvl
	$(COMPARE) -inputN=10 -spec sumNspec.cvl -impl sumNimpl.cvl

clean: 
	rm -f *~
	rm -f -r CIVLREP
