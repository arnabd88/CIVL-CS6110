CIVL=civl
VERIFY=$(CIVL) verify

all: printf fscanf fopen

printf: printf.cvl
	$(VERIFY) printf.cvl

fscanf: fscanf.cvl
	$(VERIFY) fscanf.cvl

fopen: fileOpen.cvl
	$(VERIFY) fileOpen.cvl

clean:
	rm -rf CIVLREP
	rm -rf ~
