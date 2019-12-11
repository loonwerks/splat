#include "stdio.h"

int main(int argc,char* argv[]) {
    FILE *fp = fopen("input.bin","wb");
    if(fp == NULL) {
        printf("error creating file");
        return -1;
    }

    int nl = 0x0A;
    int i,j,k;

    for (i = -90; i <= 90; i++) {
      for (j = -180; j <= 180; j++) {
        for (k = 0; k <= 150; k++) {
	  fwrite(&i, 4, 1, fp);
	  fwrite(&j, 4, 1, fp);
	  fwrite(&k, 4, 1, fp);
	  /*          fwrite(&nl, 4, 1, fp); */
	}
      }
    }


    fclose(fp);

    return 0;
}


/*
    int val = -90; fwrite(&val, 4, 1, fp);

    val = -180; fwrite(&val, 4, 1, fp);

    val = 0;  fwrite(&val, 4, 1, fp);

    val = 90; fwrite(&val, 4, 1, fp);

    val = 180; fwrite(&val, 4, 1, fp);

    val = 15000;  fwrite(&val, 4, 1, fp);
*/
