CIVL=civl
VERIFY=$(CIVL) verify

all: adderBad barrierBad blockAdderBad diningBad \
		locksBad locksBad10 spawnBad

adderBad: adderBad.cvl
	$(VERIFY) adderBad.cvl -inputB=4 -min
	$(CIVL) replay adderBad.vcl -gui //cvl
	
# Two kinds of violations are found in the following:
# a deadlock, and an assertion violation:
barrierBad: barrierBad.cvl
	$(VERIFY) -inputB=4 barrierBad.cvl -min
	$(CIVL) replay barrierBad.cvl -id=0 -gui
	$(CIVL) replay barrierBad.cvl -id=1 -gui

blockAdderBad: blockAdderBad.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdderBad.cvl -min
	$(CIVL) replay blockAdderBad.cvl -gui

diningBad: diningBad.cvl
	$(VERIFY) -inputB=4 diningBad.cvl -min
	$(CIVL) replay diningBad.cvl -gui

locksBad: locksBad.cvl
	$(VERIFY) locksBad.cvl -min
	$(CIVL) replay locksBad.cvl -gui

locksBad10: locksBad10.cvl
	$(VERIFY) locksBad10.cvl
	$(CIVL) replay locksBad10.cvl -gui

spawnBad: spawnBad.cvl
	$(VERIFY) spawnBad.cvl -inputN=10
	$(CIVL) replay spawnBad.cvl -gui

clean:
	rm -rf CIVLREP *~

