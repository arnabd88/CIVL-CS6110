//#include <omp.h>

int main (int argc, char *argv[]){
    int sum = 0, localsum=0;
    int n = 10;
    int i;
    for(i = 0; i < n; i++){
        localsum += i;
    }
    sum += localsum;
}
