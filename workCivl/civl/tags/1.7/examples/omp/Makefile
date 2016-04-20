
all: dotProduct1 dotProduct_critical dotProduct_orphan canonical-for

dotProduct1: dotProduct1.cvl
	civl verify dotProduct1.cvl

dotProduct_critical: dotProduct_critical.cvl
	civl verify dotProduct_critical.cvl

dotProduct_orphan: dotProduct_orphan.cvl
	civl verify dotProduct_orphan.cvl

fig3.10-mxv-omp: fig3.10-mxv-omp.cvl
	civl verify fig3.10-mxv-omp.cvl

canonical-for: canonicalForLoops.c
	civl verify -ompNoSimplify -input_omp_thread_max=2  canonicalForLoops.c
