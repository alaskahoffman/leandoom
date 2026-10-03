/* Unmodified pinned Nuked OPL3 is compiled separately; OPL2 melodic profile. */
#include "opl3.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int main(int argc,char **argv) {
 if(argc!=3)return 2;
 FILE *in=fopen(argv[1],"r"),*out=fopen(argv[2],"wb");if(!in||!out)return 2;
 opl3_chip chip;OPL3_Reset(&chip,44100);
 char op[8];unsigned a,b;
 while(fscanf(in,"%7s",op)==1){
  if(!strcmp(op,"w")){if(fscanf(in,"%u %u",&a,&b)!=2)return 3;OPL3_WriteReg(&chip,a,b);}
  else if(!strcmp(op,"s")){if(fscanf(in,"%u",&a)!=1)return 3;
   for(unsigned i=0;i<a;i++){int16_t pcm[2];OPL3_GenerateResampled(&chip,pcm);
    for(int c=0;c<2;c++){uint16_t n=(uint16_t)pcm[c];fputc(n&255,out);fputc(n>>8,out);}
   }
  }else return 3;
 }
 fclose(in);fclose(out);return 0;
}
