CIVL = civl
COMPARE = $(CIVL) compare

all: output

output: out1.c out2.c
	$(COMPARE) -impl out1.c -spec out2.c 

clean: 
	rm -f *~
	rm -f -r CIVLREP
