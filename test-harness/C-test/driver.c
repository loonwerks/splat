#include "stdio.h"

extern int match_foo (char * s, int len);

int main(int argc,char* argv[]) {
    FILE *fp = fopen("foo.bin","rb");
    if(fp == NULL) {
        printf("error creating file");
        return -1;
    }

    int len = 12;
    int result = -1;
    char buffer[len];

    fread(buffer, 4, 3, fp);
    fclose(fp);

    result = match_foo(buffer, len);

    if (result == 0) {
      printf("REJECT\n");
    }
    else
      if (result == 1) {
      printf("ACCEPT\n");
      }
      else {
      printf("WEIRD!\n");
      }
    return 0;
}
