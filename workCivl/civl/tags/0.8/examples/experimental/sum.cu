/**
* This is an example from the paper "Formal Semantics of Heterogeneous CUDA-C: 
* A Modular Approach with Applications" by Chris Hathhorn et al. 
*/

#include <stdio.h>
#include <cuda.h>

#define N 18
#define NBLOCKS 2
#define NTHREADS (N/NBLOCKS)

__global__ void sum(int* in, int* out) {
  extern __shared__ int shared[];
  int i, tid = threadIdx.x,
         bid = blockIdx.x,
         bdim = blockDim.x;
         
  shared[tid] = in[bid * bdim + tid];
  
  __syncthreads();
  if(tid < bdim/2) {
    shared[tid] += shared[bdim/2 + tid];
  }
  __syncthreads();
  if(tid == 0) {
    for (i = 1; i != (bdim/2) + (bdim%2); ++i) {
      shared[0] += shared[i];
    }
    out[bid] = shared[0];
  }
}

int main(void) {
  int i, *dev_in, *dev_out, host[N];
  
  printf("INPUT: ");
  for(i = 0; i != N; ++i) {
    host[i] = (21*i + 29) % 100;
    printf(" %d ", host[i]);
  }
  printf("\n");
  
  cudaMalloc(&dev_in, N * sizeof(int));
  cudaMalloc(&dev_out, NBLOCKS * sizeof(int));
  
  cudaMemcpy(dev_in, host, N * size(int),
         cudaMemcpyHostToDevice);
  sum<<<NBLOCKS, NTHREADS, NTHREADS * sizeof(int)>>>(
         dev_in, dev_out);
  sum<<<1, NBLOCKS, NBLOCKS * sizeof(int)>>>(
         dev_out, dev_out);
  cudaMemcpy(host, dev_out, sizeof(int),
         cudaMemcpyDeviceToHost);
  cudaDeviceSynchronize();
  
  printf("OUTPUT: %u\n", *host);
  cudaFree(dev_in);
  cudaFree(dev_out);
  return 0;
}

