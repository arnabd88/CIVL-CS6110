CIVL=civl
VERIFY=$(CIVL) verify
RUN=$(CIVL) run
CIVLC_PATH=./civlc/
STDIO_PATH=./stdio/
OMP_PATH=./omp/


all: assert memcpy malloc printf printfBad commFeatures commBad msgUnpackBad1 msgUnpackBad2 \
	barrier chooseInt exit exitBad intIter contains equals trans_ptr copy seq freeBad1 freeBad2 \
	bundleAndHeap domainDecomposition string \
	teams shared read write barrierFlush reduction  sections single ompfor

assert : assert.cvl
	$(VERIFY) assert.cvl

memcpy: memcpy.cvl
	$(VERIFY) memcpy.cvl

malloc: malloc.cvl
	$(VERIFY) malloc.cvl

printf: ${STDIO_PATH}printf.cvl
	$(VERIFY) ${STDIO_PATH}printf.cvl

printfBad: ${STDIO_PATH}printfBad.cvl
	$(VERIFY) ${STDIO_PATH}printfBad.cvl

commFeatures: ${CIVLC_PATH}communicatorFeatures.cvl
	$(VERIFY) -inputNPROCS_BOUND=2 -inputN_BOUND=2 ${CIVLC_PATH}communicatorFeatures.cvl

commBad: ${CIVLC_PATH}commBad.cvl
	$(VERIFY) ${CIVLC_PATH}commBad.cvl

msgUnpackBad1: ${CIVLC_PATH}messageUnpackBad1.cvl
	$(VERIFY) ${CIVLC_PATH}messageUnpackBad1.cvl

msgUnpackBad2: ${CIVLC_PATH}messageUnpackBad2.cvl
	$(VERIFY) ${CIVLC_PATH}messageUnpackBad2.cvl

barrier: ${CIVLC_PATH}barrier.cvl
	$(VERIFY) -inputB=5 ${CIVLC_PATH}barrier.cvl

chooseInt: ${CIVLC_PATH}chooseInt.cvl
	$(VERIFY) ${CIVLC_PATH}chooseInt.cvl

exit: ${CIVLC_PATH}exit.cvl
	$(VERIFY) ${CIVLC_PATH}exit.cvl

exitBad: ${CIVLC_PATH}exitBad.cvl
	$(VERIFY) ${CIVLC_PATH}exitBad.cvl

intIter: ${CIVLC_PATH}intIter.cvl
	$(VERIFY) -inputB=5 ${CIVLC_PATH}intIter.cvl

contains: ${CIVLC_PATH}contains.cvl
	$(VERIFY) ${CIVLC_PATH}contains.cvl

equals: ${CIVLC_PATH}equals.cvl
	$(VERIFY) ${CIVLC_PATH}equals.cvl

trans_ptr: ${CIVLC_PATH}translate_ptr.cvl
	$(VERIFY) ${CIVLC_PATH}translate_ptr.cvl

copy: ${CIVLC_PATH}copy.cvl
	$(VERIFY) ${CIVLC_PATH}copy.cvl

seq: ${CIVLC_PATH}seq.cvl
	$(VERIFY) ${CIVLC_PATH}seq.cvl

freeBad1: ${CIVLC_PATH}freeBad1.cvl
	$(VERIFY) ${CIVLC_PATH}freeBad1.cvl

freeBad2: ${CIVLC_PATH}freeBad2.cvl
	$(VERIFY) ${CIVLC_PATH}freeBad2.cvl

bundleAndHeap: ${CIVLC_PATH}bundleAndHeap.cvl
	$(VERIFY) ${CIVLC_PATH}bundleAndHeap.cvl

domainDecomposition: ${CIVLC_PATH}domainDecomposition.cvl
	$(VERIFY) -inputn=4 ${CIVLC_PATH}domainDecomposition.cvl

teams: ${OMP_PATH}teams.cvl
	$(RUN) ${OMP_PATH}teams.cvl

shared: ${OMP_PATH}shared.cvl
	$(RUN) ${OMP_PATH}shared.cvl

read: ${OMP_PATH}read.cvl
	$(RUN) ${OMP_PATH}read.cvl

write: ${OMP_PATH}write.cvl
	$(RUN) ${OMP_PATH}write.cvl

barrierFlush: ${OMP_PATH}barrierFlush.cvl
	$(RUN) ${OMP_PATH}barrierFlush.cvl

reduction: ${OMP_PATH}reduction.cvl
	$(RUN) ${OMP_PATH}reduction.cvl

sections: ${OMP_PATH}sections.cvl
	$(RUN) ${OMP_PATH}sections.cvl

single: ${OMP_PATH}single.cvl
	$(RUN) ${OMP_PATH}single.cvl

ompfor: ${OMP_PATH}for.cvl
	$(RUN) ${OMP_PATH}for.cvl

string: string.cvl
	$(VERIFY) string.cvl


