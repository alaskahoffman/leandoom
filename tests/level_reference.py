"""Original secret routine, switch texture routine, and selected exit-use branch."""
from pathlib import Path
from motion_reference import function

GROUPS=('secret_sectors','exit_switches','switch_palette')

def oracle_source(upstream):
    switches=upstream['src/doom/p_switch.c']
    use=function(switches,'boolean\nP_UseSpecialLine')
    # Keep both complete original use-side/nonplayer guards and only case 11.
    prefix=use[:use.index('    // do something')]
    case=use[use.index('      case 11:'):use.index('      case 14:')]
    use=prefix+'    switch (line->special) {\n'+case+'    }\n    return true;\n}\n'
    table=switches[switches.index('switchlist_t alphSwitchList[]'):switches.index('int\t\tswitchlist')]
    routines=table+function(switches,'void P_InitSwitchList')
    routines+=function(upstream['src/doom/g_game.c'],'void G_ExitLevel')
    routines+=function(switches,'void\nP_ChangeSwitchTexture')+use
    routines+=function(upstream['src/doom/p_spec.c'],'void P_PlayerInSpecialSector')
    spawn=upstream['src/doom/p_spec.c']
    start=spawn.index('\t  case 9:',spawn.index('void P_SpawnSpecials'))
    count=spawn[start:spawn.index('\t  case 10:',start)]
    routines+='static void count_secret(int special) { switch(special) {\n'+count+'}}\n'
    return (Path(__file__).parent/'reference/level_fixture.c').read_text().replace('/* ROUTINES */',routines)

def corpus():
    secret=[]
    edges=(-2147483648,-65536,-1,0,1,65536,2147483647)
    for z in edges:
        for floor in edges:
            for count in (-2147483648,-1,0,1,3,2147483647):
                secret += [f'secret {z} {floor} 9 {count}',f'visit {floor} {floor}',f'visit {floor} {floor}']
    for specials in ([],[9],[0,1,7,8,9,12,9,9],list(range(256)),[9]*1024):
        secret += ['total '+str(len(specials))+''.join(f' {n}' for n in specials)]
    # Earlier switch-table entries win even when placed in lower-priority slots;
    # duplicate texture IDs reproduce aliasing, with both SW1 and SW2 directions.
    exits=[]
    palettes=([],[10,11],[30,31,10,11],[10,11,10,12],[0,1,2,3,4,5])
    for palette in palettes:
        values=sorted(set([-1,0,10,11,30,31]+palette))
        for a in values:
            for b in values:
                for c in values:
                    for player,side,flags in ((1,0,0),(1,0,32),(0,0,0),(0,0,32),(1,1,0)):
                        exits.append(f'exit {player} {side} {flags} 11 {a} {b} {c} {len(palette)}'+''.join(f' {x}' for x in palette))
    return dict(zip(GROUPS,(secret,exits,[f'palette {n}' for n in (1,2,3)])))
