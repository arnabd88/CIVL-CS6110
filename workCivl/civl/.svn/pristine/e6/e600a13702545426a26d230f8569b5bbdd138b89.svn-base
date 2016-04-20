CIVL=civl
VERIFY=$(CIVL) verify

adder: adder.cvl
	$(VERIFY) adder.cvl -inputB=5

adderBad: adderBad.cvl
	$(VERIFY) adderBad.cvl -inputB=4 -min
	$(CIVL) replay adderBad.cvl

blockAdder: blockAdder.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdder.cvl

blockAdderBad: blockAdderBad.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdderBad.cvl -min
	$(CIVL) replay blockAdderBad.cvl

bank: bank.cvl
	$(VERIFY) bank.cvl

barrier: barrier.cvl
	$(VERIFY) -inputB=4 barrier.cvl

# Two kinds of violations are found in the following:
# a deadlock, and an assertion violation:
barrierBad: barrierBad.cvl
	$(VERIFY) -inputB=4 barrierBad.cvl -min
	$(CIVL) replay barrierBad.cvl -id=0
	$(CIVL) replay barrierBad.cvl -id=1

barrier2: barrier2.cvl
	$(VERIFY) barrier2.cvl

dining: dining.cvl
	$(VERIFY) -inputB=4 dining.cvl

diningBad: diningBad.cvl
	$(VERIFY) -inputB=4 diningBad.cvl -min
	$(CIVL) replay diningBad.cvl


clean:
	rm -rf CIVLREP *~

