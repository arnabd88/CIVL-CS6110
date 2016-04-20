
CIVL=civl
VERIFY=$(CIVL) verify

all: arrayWrite mallocInputArray printExpr quantified returnNull showTrans sizeOfTypes

arrayWrite: arrayWrite.cvl
	$(VERIFY) arrayWrite.cvl

mallocInputArray: mallocInputArray.cvl
	$(VERIFY) mallocInputArray.cvl

printExpr: printExpr.cvl
	$(VERIFY) printExpr.cvl

quantified: quantified.cvl
	$(VERIFY) quantified.cvl

returnNull: returnNull.cvl
	$(VERIFY) returnNull.cvl

showTrans: showTrans.cvl
	$(VERIFY) showTrans.cvl

sizeOfTypes: sizeOfTypes.c
	$(VERIFY) sizeOfTypes.c