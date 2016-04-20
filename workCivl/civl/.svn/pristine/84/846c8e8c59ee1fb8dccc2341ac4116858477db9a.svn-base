//http://www.arc.vt.edu/resources/software/cuda/docs/cuda-omp.cu

#include <omp.h>
#include <cuda.h>
#include <stdio.h>      
#include <stdlib.h>      


#ifdef _CIVL
$input int BLOCKS;
$input int BLOCK_B;
$assume 1 <= BLOCKS && BLOCKS <= BLOCK_B;
$input int THREADS_PER_BLOCK;
$input int THREADS_B;
$assume 1 <= THREADS_PER_BLOCK && THREADS_PER_BLOCK <= THREADS_B;
#else
#define BLOCKS 64
#define THREADS_PER_BLOCK 128
#endif

// A kernel that increments each array element by the value b

__global__ void kernelAddConstant(int *g_a, const int b)
{
	int idx = blockIdx.x * blockDim.x + threadIdx.x;
	g_a[idx] += b;
}

// Check whether each element was incremented by the value b
int correctResult(int *data, const int n, const int b)
{
	for(int i = 0; i < n; i++)
        	if(data[i] != i + b)
                	return 0;
	return 1;
}

int main(int argc, char *argv[])
{
#ifdef _CIVL
	elaborate(BLOCKS);
	elaborate(THREADS_PER_BLOCK);
#endif

	// Variable which holds number of GPUs
	int num_gpus = 0;   

	// Determine the number of CUDA capable GPUs
        cudaGetDeviceCount(&num_gpus);
        if(num_gpus < 1)
        {
                printf("No CUDA Capable GPU(s) Detected \n");
                return 1;
        }

        // Display the CPU and GPU processor specification         
	int num_procs = omp_get_num_procs();
	printf("number of host CPUs:\t%d\n", num_procs);
    	printf("number of CUDA devices:\t%d\n", num_gpus);
	for(int i = 0; i < num_gpus; i++)
    	{
        	cudaDeviceProp dprop;
        	cudaGetDeviceProperties(&dprop, i);
                printf("\t Device %d is a %s\n", i, dprop.name);
    	}


	// Initialize the variables 
    	unsigned int n = num_gpus * THREADS_PER_BLOCK * BLOCKS;
    	unsigned int nbytes = n * sizeof(int);
        int *a = 0;             // pointer to data on the CPU
        int b = 3;              // value by which each array array element will be incremented
        a = (int*)malloc(nbytes);
        
	if(0 == a)
        {
                printf("couldn't allocate CPU memory\n");
                return 1;
        }
        
	for(unsigned int i = 0; i < n; i++)
        	a[i] = i;
    
	// Set the number of threads to the number of GPUs on the system
	omp_set_num_threads(num_gpus);

	#pragma omp parallel
    	{
        	unsigned int cpu_thread_id = omp_get_thread_num();
                unsigned int num_cpu_threads = omp_get_num_threads();

                // Assign and check the GPU device for each thread
                int gpu_id = -1;
                cudaSetDevice(cpu_thread_id % num_gpus);        
                cudaGetDevice(&gpu_id);

                printf("CPU thread %d (of %d) uses CUDA device %d\n", cpu_thread_id, num_cpu_threads, gpu_id);

		// Variable on the device associated with this CPU thread
                int *d_a = 0; 

		// Variable for the CPU
                int *sub_a = a + cpu_thread_id * n / num_cpu_threads;
   
                unsigned int nbytes_per_kernel = nbytes / num_cpu_threads;
                dim3 gpu_threads = {THREADS_PER_BLOCK, 1, 1};  // 128 threads per block
                dim3 gpu_blocks = {(n / (gpu_threads.x * num_cpu_threads)), 1, 1};

		//Allocate memory on the device
          	cudaMalloc((void**)&d_a, nbytes_per_kernel);

		//Initialize the array on the device with zeros
          	cudaMemset(d_a, 0, nbytes_per_kernel);

		//Copy data from host to device
	       	cudaMemcpy(d_a, sub_a, nbytes_per_kernel, cudaMemcpyHostToDevice);
	
		//Launch the kernel
        	kernelAddConstant<<<gpu_blocks, gpu_threads>>>(d_a, b);

		//Copy the result  from the device to the host
          	cudaMemcpy(sub_a, d_a, nbytes_per_kernel, cudaMemcpyDeviceToHost);
          
		//Deallocate the memory on the device
		cudaFree(d_a);

	}
        

        if(cudaSuccess != cudaGetLastError()) {
		int err_num = cudaGetLastError();
		const char * err_str = cudaGetErrorString(err_num);
		printf("%s\n", err_str);
	}


	//Check for correctness of the result
    	if(correctResult(a, n, b)) {
#ifdef _CIVL
		$assert($true);
#endif
        	printf("Test PASSED\n");
    	} else
        	printf("Test FAILED\n");

	//Deallocate the CPU memory 
	free(a);    

	// deprecated
    	// cudaThreadExit();

    	return 0;
}

