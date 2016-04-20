CIVL=civl
VERIFY=$(CIVL) verify

all: dotProduct dotProduct_critical fig4.98-threadprivate 
	
dotProduct: dotProduct.cvl
	$(VERIFY) -inputNTHREADS=3 -inputN=8 dotProduct.cvl
	
dotProduct_critical: dotProduct_critical.cvl
	$(VERIFY) -inputNTHREADS=2 -inputN=8 dotProduct_critical.cvl
	
fig4.98-threadprivate: fig4.98-threadprivate.cvl
	$(VERIFY) -inputTHREADS_BOUND=2 -inputN_BOUND=4 -enablePrintf=false fig4.98-threadprivate.cvl
