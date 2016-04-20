
CIVL=civl
VERIFY=$(CIVL) verify

all: badDivideByZero badIndexOutOfBound

badDivideByZero: badDivideByZero.f
	$(VERIFY) badDivideByZero.f

badIndexOutOfBound: badIndexOutOfBound.f
	$(VERIFY) badIndexOutOfBound.f

clean:
	rm -rf CIVLREP *~



