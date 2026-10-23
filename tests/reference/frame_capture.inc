/* One deterministic presentation after the requested final tic.
 * Renderer/HUD routines are unchanged; video presentation and gamma are bypassed.
 * SPDX-License-Identifier: GPL-2.0-or-later */
#include <stdio.h>
#include "i_video.h"
#include "r_main.h"
#include "st_stuff.h"
#include "hu_stuff.h"
extern unsigned char LRenderPalette[768];
static void LRenderCapture(void)
{
    const char *path=getenv("LEANDOOM_FRAME");
    FILE *file;
    int i;
    if(!path) I_Error("frame capture: missing output path");
    R_SetViewSize(10,0);
    R_ExecuteSetViewSize();
    R_RenderPlayerView(&players[0]);
    ST_Drawer(false,true);
    HU_Drawer();
    file=fopen(path,"wb");
    if(!file) I_Error("frame capture: cannot open output");
    fprintf(file,"P6\n320 200\n255\n");
    for(i=0;i<320*200;++i)
        if(fwrite(LRenderPalette+I_VideoBuffer[i]*3,1,3,file)!=3)
            I_Error("frame capture: write failed");
    if(fclose(file)) I_Error("frame capture: close failed");
}
