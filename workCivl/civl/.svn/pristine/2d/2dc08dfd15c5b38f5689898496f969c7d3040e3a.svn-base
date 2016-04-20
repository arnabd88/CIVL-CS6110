
CIVL = java -jar ../civl.jar

TARGETS = \
	minimal \
	spawn \
	locks \
	sideEffects \
	sideEffects2 \
	adder \
	matmat

default: all

all: $(TARGETS)

minimal: minimal.cvl
	$(CIVL) minimal.cvl

spawn: spawn.cvl
	$(CIVL) spawn.cvl

locks: locks.cvl
	$(CIVL) locks.cvl

sideEffects: sideEffects.cvl
	$(CIVL) sideEffects.cvl

sideEffects2: sideEffects2.cvl
	$(CIVL) sideEffects2.cvl

adder: adder.cvl
	$(CIVL) adder.cvl

matmat: matmat.cvl
	$(CIVL) matmat.cvl
