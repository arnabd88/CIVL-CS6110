#include<stdio.h>
#include<stdlib.h>

int sum=0;
char* c;

int main(){
    if(!c)
      sum=1;
    printf("%d\n", sum);
    c=malloc(sizeof(char));
    if(!(c[0]=='a'))
      sum=2;
    printf("%d\n", sum);
    free(c);
}
