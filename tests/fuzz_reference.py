"""Unchanged R_DrawFuzzColumn over mutable palette-index buffers."""
from pathlib import Path
from motion_reference import function

GROUPS=('fuzz_columns','fuzz_sequences')

def oracle_source(upstream):
    source=upstream['src/doom/r_draw.c']
    table=source[source.index('#define FUZZTABLE'):source.index('//\n// Framebuffer postprocessing.')]
    fixture=(Path(__file__).parent/'reference/fuzz_fixture.c').read_text()
    return fixture.replace('/* FUZZ_TABLE */',table).replace('/* FUZZ_FUNCTION */',function(source,'void R_DrawFuzzColumn'))

def corpus():
    columns=[]
    for phase in range(50):
        for height in (3,32,168,200):
            for low,high in ((0,height-1),(0,0),(height-1,height-1),(1,1),(height,0),(0,-1)):
                x=(phase*17+height)%320
                columns += [f'reset {phase*5%256} {phase} {height%4}',f'draw {x} {low} {high} {height}']
    sequences=[]
    for variant in range(4):
        sequences += [f'reset {variant*41} 49 {variant}']
        # The same phase/buffer are reused across posts and simulated frames.
        for frame in range(5):
            for x in (0,319,160,161,160):
                for low,high in ((0,199),(12,47),(49,198),(100,100)):
                    sequences += [f'draw {x} {low} {high} 200']
            sequences += ['snapshot']
    return dict(zip(GROUPS,(columns,sequences)))
