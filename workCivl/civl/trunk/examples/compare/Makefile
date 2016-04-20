all: sumN add diff1d maxN output queueT simpleT svector

sumN: sum/Makefile
	cd sum && make

add: adder/Makefile
	cd adder && make

diff1d: diffusion1d/Makefile
	cd diffusion1d && make

dotP: dot/Makefile
	cd dot && make

maxN: max/Makefile
	cd max && make

output: io/Makefile
	cd io && make

queueT: queue/Makefile
	cd queue && make

clean: 
	rm -f *~
	rm -f -r CIVLREP
