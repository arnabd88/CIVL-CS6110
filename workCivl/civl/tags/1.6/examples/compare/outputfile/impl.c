#include<stdio.h>
#include<stdlib.h>

int main(){
  FILE *f = fopen("file.txt", "w");
  if (f == NULL){
    printf("Error opening file!\n");
    exit(1);
  }
  char c = 'A';
  fprintf(f, "A character: %c\n", c);
  fclose(f);
}
