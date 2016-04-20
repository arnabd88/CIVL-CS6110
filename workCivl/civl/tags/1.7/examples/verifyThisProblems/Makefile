CIVL=civl
VERIFY=$(CIVL) verify

all: dancingLinks lcp lrs parallelGCD quantifiedComp \
relaxedPrefix

dancingLinks:
	$(VERIFY) dancingLinks.c

lcp:
	$(VERIFY) lcp.c

lrs:
	$(VERIFY) lrs.c

parallelGCD:
	$(VERIFY) parallelGCD.c

quantifiedComp:
	$(VERIFY) quantifiedComp.cvl

relaxedPrefix:
	$(VERIFY) relaxedPrefix.c
