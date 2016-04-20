CIVL=civl
VERIFY=$(CIVL) verify

all: adder adderBad bank barrier barrier2 \
	barrierBad blockAdder blockAdderBad dining \
	diningBad locksBad locksBad10 locksGood \
	spawn spawn2 spawnBad

adder: adder.cvl
	$(VERIFY) adder.cvl -inputB=5

adderBad: adderBad.cvl
	$(VERIFY) adderBad.cvl -inputB=4 -min
	$(CIVL) replay adderBad.cvl
	
bank: bank.cvl
	$(VERIFY) bank.cvl -inputNUM_ACCOUNTS=3
	
barrier: barrier.cvl
	$(VERIFY) -inputB=4 barrier.cvl

barrier2: barrier2.cvl
	$(VERIFY) -inputB=4 barrier2.cvl
	
# Two kinds of violations are found in the following:
# a deadlock, and an assertion violation:
barrierBad: barrierBad.cvl
	$(VERIFY) -inputB=4 barrierBad.cvl -min
	$(CIVL) replay barrierBad.cvl -id=0
	$(CIVL) replay barrierBad.cvl -id=1

blockAdder: blockAdder.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdder.cvl

blockAdderBad: blockAdderBad.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdderBad.cvl -min
	$(CIVL) replay blockAdderBad.cvl

dining: dining.cvl
	$(VERIFY) -inputB=4 dining.cvl

diningBad: diningBad.cvl
	$(VERIFY) -inputB=4 diningBad.cvl -min
	$(CIVL) replay diningBad.cvl

locksBad: locksBad.cvl
	$(VERIFY) locksBad.cvl

locksBad10: locksBad10.cvl
	$(VERIFY) locksBad10.cvl
	
locksGood: locksGood.cvl
	$(VERIFY) locksGood.cvl
	
spawn: spawn.cvl
	$(VERIFY) spawn.cvl -inputN=10
	
spawn2: spawn2.cvl
	$(VERIFY) spawn2.cvl -inputN=10

spawnBad: spawnBad.cvl
	$(VERIFY) spawnBad.cvl -inputN=10

clean:
	rm -rf CIVLREP *~

