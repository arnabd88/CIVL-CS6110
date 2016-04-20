
CIVL=civl
VERIFY=$(CIVL) verify

TARGETS = \
	collective \
	contract \
	count \
	floatsum \
	floatsum2 \
	gaussElim \
	multInLoopCond \
	pathfinder_cuda
	
default: all

all: $(TARGETS)

collective: collective.cvl
	$(VERIFY) collective.cvl
	
contract: contract.cvl
	$(VERIFY) contract.cvl
	
count: count.cvl
	$(VERIFY) count.cvl
	
floatsum: floatsum.cvl
	$(VERIFY) floatsum.cvl
	
floatsum2: floatsum2.cvl
	$(VERIFY) floatsum2.cvl
	
gaussElim: gaussElim.cvl
	$(VERIFY) -inputN_BOUND=3 -inputM_BOUND=3 gaussElim.cvl
	
multInLoopCond: multInLoopCond.cvl
	$(VERIFY) multInLoopCond.cvl
	
pathfinder_cuda: pathfinder_cuda.cvl
	$(VERIFY) pathfinder_cuda.cvl
