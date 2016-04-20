CIVL=civl
VERIFY=$(CIVL) verify

all: derivative derivativeBackward derivativeBad diffusion laplace2d secondDerivative \
	secondDerivativeBad upwindFirstOrder upwindSecondOrder upwindThirdOrder

derivative:
	$(VERIFY) -inputnum_elements=5 derivative.cvl

derivativeBackward:
	$(VERIFY) -inputnum_elements=5 derivativeBackward.cvl

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

upwindFirstOrder:
	$(VERIFY) -inputn=4 upwindFirstOrder.cvl

upwindSecondOrder:
	$(VERIFY) -inputn=5 upwindSecondOrder.cvl

upwindThirdOrder:
	$(VERIFY) -inputn=5 upwindThirdOrder.cvl
