#include <stdio.h>

int factorial (int my_input) {
  int result;

  if (my_input<=1) { result=1; }
  else {
    result = my_input*factorial(my_input-1);
  }   
  printf("We are inside.  my_input=%0d. result=%0d\n",my_input, result);
  return result;
}

void tell_story (void){
  printf("Once upon a time.....\n");
  printf("...\n");
  printf("is there any way in a c program to tell what function a printf came from?\n");
  printf("\n");
  printf("          el fin.\n");
}

int main(void){
  //factorial(400);
}
