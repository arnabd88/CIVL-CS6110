CIVL=civl
VERIFY=$(CIVL) verify

all: derivative derivativeBad diffusion laplace2d secondDerivative \
	secondDerivativeBad
	
derivative:
	$(VERIFY) -inputnum_elements=5 derivative.cvl
	
derivativeBad:
	$(VERIFY) -inputnum_elements=5 derivativeBad.cvl
	
diffusion:
	$(VERIFY) -inputn=4 diffusion.cvl
	
laplace2d:
	$(VERIFY) -inputrows=3 -inputcols=3 laplace2d.cvl
	
secondDerivative:
	$(VERIFY) -inputnum_elements=5 secondDerivative.cvl
	
secondDerivativeBad:
	$(VERIFY) -inputnum_elements=5 secondDerivativeBad.cvl
