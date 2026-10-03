/* Full-resolution 320x200 framebuffer, view origin zero. Low detail is excluded. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#define SCREENWIDTH 320
#define SCREENHEIGHT 200
typedef unsigned char pixel_t;
static pixel_t pixels[320*200],maps[7*256],*colormaps=maps,*ylookup[200];
static int columnofs[320],dc_x,dc_yl,dc_yh,viewheight;
/* FUZZ_TABLE */
/* FUZZ_FUNCTION */
static void reset(int seed,int phase,int variant) {
    assert(seed>=0&&seed<256&&phase>=0&&phase<50&&variant>=0&&variant<4);
    for(int y=0;y<200;y++) {
        ylookup[y]=pixels+y*320;
        for(int x=0;x<320;x++)pixels[y*320+x]=(x*17+y*13+y/2*7+seed)%256;
    }
    for(int x=0;x<320;x++)columnofs[x]=x;
    for(int i=0;i<7*256;i++)maps[i]=(i*73+i/256*11+variant*19)%256;
    fuzzpos=phase;
}
int main(int argc,char **argv) {
    assert(argc==2);FILE *in=fopen(argv[1],"r");assert(in);reset(0,0,0);
    char line[256],op[24];int a,b,c,d;
    while(fgets(line,sizeof(line),in)) {
        int n=sscanf(line,"%23s %d %d %d %d",op,&a,&b,&c,&d);
        if(n==4&&!strcmp(op,"reset")) {reset(a,b,c);puts("reset");}
        else if(n==5&&!strcmp(op,"draw")) {
            assert(a>=0&&a<320&&d>=3&&d<=200&&b>=0&&b<=d&&c>=-1&&c<d);
            dc_x=a;dc_yl=b;dc_yh=c;viewheight=d;R_DrawFuzzColumn();
            printf("%d %d %d",fuzzpos,dc_yl,dc_yh);
            for(int y=0;y<200;y++)printf(" %u",pixels[y*320+a]);
            putchar('\n');
        } else if(n==1&&!strcmp(op,"snapshot")) {
            uint64_t hash=UINT64_C(14695981039346656037);
            for(int i=0;i<320*200;i++)hash=(hash^pixels[i])*UINT64_C(1099511628211);
            printf("%d %llu\n",fuzzpos,(unsigned long long)hash);
        } else abort();
    }
    fclose(in);return 0;
}
