
CIVL=civl
VERIFY=$(CIVL) verify

all: algebra assoc derivative diffusion division \
	divisionBad laplace matmat matmatBad mean meanBad \
	multiplicationInLoopCondition sqrt sqrtBad1 sqrtBad2 quadratic1
	quadratic2

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

sqrt: sqrt.cvl
	$(VERIFY) sqrt.cvl

sqrtBad1: sqrtBad1.cvl
	$(VERIFY) sqrtBad1.cvl

sqrtBad2: sqrtBad2.cvl
	$(VERIFY) sqrtBad2.cvl

quadratic1: quadratic1.cvl
	$(VERIFY) quadratic1.cvl

quadratic2: quadratic2.cvl
	$(VERIFY) quadratic2.cvl

clean:
	rm -rf CIVLREP *~



