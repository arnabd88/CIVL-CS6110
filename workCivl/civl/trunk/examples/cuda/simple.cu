__global__ void simple() {
}

int main(void) {
	simple<<<1, 1, 0>>>();
	return 0;
}


