
CIVL=civl
VERIFY=$(CIVL) verify

all: algebra assoc derivative diffusion division \
	divisionBad laplace matmat matmatBad mean meanBad \
	multiplicationInLoopCondition

algebra: algebra.cvl
	$(VERIFY) algebra.cvl

assoc: assoc.cvl
	$(VERIFY) -inputB=10 assoc.cvl
	
derivative: derivative.cvl
	$(VERIFY) derivative.cvl
	
diffusion: diffusion.cvl
	$(VERIFY) diffusion.cvl

division: division.cvl
	$(VERIFY) division.cvl

divisionBad: divisionBad.cvl
	$(VERIFY) divisionBad.cvl
	$(CIVL) replay divisionBad.cvl

laplace: laplace.cvl
	$(VERIFY) laplace.cvl
	
matmat: matmat.cvl
	$(VERIFY) -inputBOUND=3 matmat.cvl

matmatBad: matmatBad.cvl
	$(VERIFY) -min -inputBOUND=3 matmatBad.cvl
	$(CIVL) replay matmatBad.cvl
	
mean: mean.cvl
	$(VERIFY) -inputB=10 mean.cvl

meanBad: meanBad.cvl
	$(VERIFY) -min -inputB=10 meanBad.cvl
	$(CIVL) replay meanBad.cvl
	
multiplicationInLoopCondition: multiplicationInLoopCondition.cvl
	$(VERIFY) multiplicationInLoopCondition.cvl

clean:
	rm -rf CIVLREP *~



