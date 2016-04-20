CIVL=civl
VERIFY=$(CIVL) verify

all: assertEquals assertEquals2  assertEqualsFail assertEqualsFail2

assertEquals: simpleAssertEquals.cvl
	$(VERIFY) simpleAssertEquals.cvl

assertEquals2: simpleAssertEquals2.cvl
	$(VERIFY) simpleAssertEquals2.cvl

assertEqualsFail: simpleAssertEqualsFail.cvl
	$(VERIFY) simpleAssertEqualsFail.cvl

assertEqualsFail2: simpleAssertEqualsFail2.cvl
	$(VERIFY) simpleAssertEqualsFail2.cvl

clean:
	rm -f *~ 
	rm -r CIVLREP