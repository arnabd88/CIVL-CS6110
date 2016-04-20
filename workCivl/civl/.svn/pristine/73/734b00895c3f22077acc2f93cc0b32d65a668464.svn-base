
# CIVL = java -jar ../civl.jar
CIVL = civl

TARGETS = \
	minimal \
	spawn \
	locks \
	sideEffects \
	sideEffects2 \
	adder \
	matmat \
	barrier \
	barrier2

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

barrier: barrier.cvl
	$(CIVL) barrier.cvl

barrier2: barrier2.cvl
	$(CIVL) barrier2.cvl
