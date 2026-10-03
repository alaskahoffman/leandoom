"""Original colormap-selection statements in a fixture, not a rasterizer oracle.

Geometric projection and distance lighting are supplied by the harness. The
copied blocks retain fixed-map, fullbright, sky and fuzz precedence unchanged.
"""
from pathlib import Path
from motion_reference import function


def oracle_extension(upstream):
    main = function(upstream['src/doom/r_main.c'], 'void R_SetupFrame')
    setup = main[main.index('    if (player->fixedcolormap)'):main.index('    framecount++')]
    plane = function(upstream['src/doom/r_plane.c'], 'void\nR_MapPlane')
    plane = plane[plane.index('    if (fixedcolormap)'):plane.index('    ds_y = y;')]
    project = function(upstream['src/doom/r_things.c'], 'void R_ProjectSprite')
    sprite = project[project.index('    if (thing->flags & MF_SHADOW)'):project.rfind('}')]
    psprite = function(upstream['src/doom/r_things.c'], 'void R_DrawPSprite')
    weapon = psprite[psprite.index('    if (viewplayer->powers[pw_invisibility]'):psprite.index('    R_DrawVisSprite')]
    sky_source = function(upstream['src/doom/r_plane.c'], 'void R_DrawPlanes')
    sky = sky_source[sky_source.index('    dc_colormap = colormaps;'):sky_source.index('    dc_texturemid = skytexturemid;')]
    masked_source = function(upstream['src/doom/r_segs.c'], 'void\nR_RenderMaskedSegRange')
    masked = masked_source[masked_source.index('    if (fixedcolormap)'):masked_source.index('    // draw the columns')]
    fixture = (Path(__file__).parent/'reference/lighting_fixture.c').read_text()
    for name, code in (('SETUP',setup),('PLANE',plane),('SPRITE',sprite),('WEAPON',weapon),('SKY',sky),('MASKED',masked)):
        fixture=fixture.replace('/* '+name+' */',code)
    return fixture


def corpus():
    commands=[]
    for fixed in (0,1,32):
        for normal in range(32):
            for fullbright in (0,1):
                for shadow in (0,1):
                    for kind in range(6):
                        commands.append(f'light {kind} {fixed} {normal} {fullbright} {shadow} 0')
            for invisibility in (-2147483648,-129,-8,-1,0,1,7,8,9,127,128,129,2100,2147483647):
                for fullbright in (0,1):
                    commands.append(f'light 4 {fixed} {normal} {fullbright} 0 {invisibility}')
    return commands
