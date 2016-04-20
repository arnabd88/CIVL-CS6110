
CIVL=civl
VERIFY=$(CIVL) verify

all: algebra assoc division divisionBad matmat2 matmat2bad \
     meanBad mean

algebra: algebra.cvl
	$(VERIFY) algebra.cvl

assoc: assoc.cvl
	$(VERIFY) -inputB=10 assoc.cvl

division: division.cvl
	$(VERIFY) division.cvl

divisionBad: divisionBad.cvl
	$(VERIFY) divisionBad.cvl
	$(CIVL) replay divisionBad.cvl

matmat2: matmat2.cvl
	$(VERIFY) matmat2.cvl -inputBOUND=3

matmat2bad: matmat2bad.cvl
	$(VERIFY) -min matmat2bad.cvl -inputBOUND=3
	$(CIVL) replay matmat2bad.cvl

meanBad: meanBad.cvl
	$(VERIFY) -min -inputB=10 meanBad.cvl
	$(CIVL) replay meanBad.cvl

mean: mean.cvl
	$(VERIFY) -inputB=10 mean.cvl



clean:
	rm -rf CIVLREP *~



