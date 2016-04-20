CIVL=civl
VERIFY=$(CIVL) verify

all: adder adderBad bank barrier barrier2 \
	barrierBad blockAdder blockAdderBad dining \
	diningBad locksBad locksBad10 locksGood \
	spawn spawn2 spawnBad

adder: adder.cvl
	$(VERIFY) -inputB=5 adder.cvl

adderBad: adderBad.cvl
	$(VERIFY) -inputB=4 -min adderBad.cvl
	$(CIVL) replay adderBad.cvl

bank: bank.cvl
	$(VERIFY) -inputNUM_ACCOUNTS=3 bank.cvl

barrier: barrier.cvl
	$(VERIFY) -inputB=4 barrier.cvl

barrier2: barrier2.cvl
	$(VERIFY) -inputB=4 barrier2.cvl
	
# Two kinds of violations are found in the following:
# a deadlock, and an assertion violation:
barrierBad: barrierBad.cvl
	$(VERIFY) -inputB=4 -min barrierBad.cvl 
	$(CIVL) replay -id=0 barrierBad.cvl 
	$(CIVL) replay -id=1 barrierBad.cvl

blockAdder: blockAdder.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdder.cvl

blockAdderBad: blockAdderBad.cvl
	$(VERIFY) -inputB=6 -inputW=3 -min blockAdderBad.cvl
	$(CIVL) replay blockAdderBad.cvl

dining: dining.cvl
	$(VERIFY) -inputB=4 dining.cvl

diningBad:
	$(VERIFY) -inputB=4 -min diningBad.cvl
	$(CIVL) replay diningBad.cvl

locksBad: locksBad.cvl
	$(VERIFY) locksBad.cvl

locksBad10: locksBad10.cvl
	$(VERIFY) locksBad10.cvl
	
locksGood: locksGood.cvl
	$(VERIFY) locksGood.cvl
	
spawn: spawn.cvl
	$(VERIFY) -inputN=10 spawn.cvl 
	
spawn2: spawn2.cvl
	$(VERIFY) -inputN=10 spawn2.cvl

spawnBad: spawnBad.cvl
	$(VERIFY) -inputN=10 spawnBad.cvl

clean:
	rm -rf CIVLREP *~

