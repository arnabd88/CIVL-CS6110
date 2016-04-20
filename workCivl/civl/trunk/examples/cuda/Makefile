CIVL=civl
VERIFY=${CIVL} verify -enablePrintf=false 

all: dot sum cudaOmp matMult1 simple vadd

sum: sum.cu
	${VERIFY} -inputN=8 -inputNBLOCKS=4 $<

dot: dot.cu
	${VERIFY} -inputN_B=6 -inputthreadsPerBlock_B=4 $<

cudaOmp: cuda-omp.cu
	${VERIFY} -inputBLOCK_B=4 -inputTHREADS_B=2 $<

matMult1: matMult1.cu
	${VERIFY} -inputN=2 -inputTILE_WIDTH=1 $<

vadd: vectorAdd.cu
	${VERIFY} $<

simple: simple.cu
	${VERIFY} $<

clean: 
	rm -f -r CIVLREP
	rm -f *~
