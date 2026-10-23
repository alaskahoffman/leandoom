/* Live presentation adapter. Gameplay/render routines remain upstream.
 * Commands are injected at the demo input boundary, before G_Ticker processing.
 * The reply descriptor is separate from Chocolate's console output.
 * SPDX-License-Identifier: GPL-2.0-or-later */
#include <stdio.h>
#include <unistd.h>
#include "i_video.h"
#include "r_main.h"
#include "st_stuff.h"
#include "hu_stuff.h"
extern unsigned char LRenderPalette[768];
static void LLiveCommand(ticcmd_t *cmd)
{
    int f,s,a,b;
    int n=scanf("%d %d %d %d",&f,&s,&a,&b);
    if(n==EOF) exit(0);
    if(n!=4 || f < -127 || f > 127 || s < -128 || s > 127 ||
       a < -32768 || a > 32512 || a%256 || b < 0 || b > 255)
        I_Error("live comparison: invalid command");
    memset(cmd,0,sizeof(*cmd));
    cmd->forwardmove=f;cmd->sidemove=s;cmd->angleturn=a;cmd->buttons=b;
}
static void LLiveFrame(FILE *reply)
{
    unsigned char rgb[320*200*3];
    int i;
    static int initialized;
    if(!initialized) {
        R_SetViewSize(10,0);
        R_ExecuteSetViewSize();
        initialized=1;
    }
    R_RenderPlayerView(&players[0]);
    ST_Drawer(false,false);
    HU_Drawer();
    for(i=0;i<320*200;++i)
        memcpy(rgb+3*i,LRenderPalette+3*I_VideoBuffer[i],3);
    if(fwrite(rgb,1,sizeof(rgb),reply)!=sizeof(rgb) || fflush(reply))
        I_Error("live comparison: reply failed");
}
