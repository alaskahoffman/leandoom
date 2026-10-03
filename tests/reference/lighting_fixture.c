/* Supplied normal-light tables isolate selection from unported raster geometry.
 * Pointer subtraction reports the chosen row; NULL reports the fuzz draw path. */
static int light_choice(int kind,int fixed,int ordinary,int fullbright,int shadow,int invisibility) {
    enum { MAXLIGHTSCALE=48,MAXLIGHTZ=128,LIGHTSCALESHIFT=12,LIGHTZSHIFT=20,
           FF_FULLBRIGHT=32768 };
    unsigned char maps[33*256],*colormaps=maps,*fixedcolormap=NULL;
    unsigned char *scalelightfixed[MAXLIGHTSCALE],*normal[MAXLIGHTSCALE],**walllights=normal;
    unsigned char *spritelights[MAXLIGHTSCALE],*planezlight[MAXLIGHTZ];
    for(int j=0;j<MAXLIGHTSCALE;j++)normal[j]=spritelights[j]=colormaps+ordinary*256;
    for(int j=0;j<MAXLIGHTZ;j++)planezlight[j]=colormaps+ordinary*256;
    struct { int fixedcolormap,powers[6]; } data={.fixedcolormap=fixed},*player=&data,*viewplayer=&data;
    data.powers[pw_invisibility]=invisibility;
    struct { int flags,frame; } thing_data={shadow?MF_SHADOW:0,fullbright?FF_FULLBRIGHT:0},*thing=&thing_data;
    struct { unsigned char *colormap; } visible={0},*vis=&visible;
    struct { int frame; } state={fullbright?FF_FULLBRIGHT:0};
    struct { __typeof__(state) *state; } psprite={&state},*psp=&psprite;
    int i,index,xscale=0,detailshift=0,distance=0;
    unsigned char *ds_colormap=NULL,*dc_colormap=colormaps+ordinary*256,*selected;
    /* SETUP */
    switch(kind) {
    case 0: selected=walllights[0];break;
    case 1:
        /* PLANE */
        selected=ds_colormap;break;
    case 2:
        /* SKY */
        selected=dc_colormap;break;
    case 3:
        /* SPRITE */
        selected=vis->colormap;break;
    case 4:
        /* WEAPON */
        selected=vis->colormap;break;
    case 5:
        /* MASKED */
        selected=dc_colormap;break;
    default: abort();
    }
    return selected?(int)(selected-colormaps)/256:-1;
}
