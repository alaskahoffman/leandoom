# Tick-by-tick demo comparison

`scripts/compare-original-demo` runs the unchanged original DOS executable as the
behavioral reference, with Lean and Chocolate Doom as two separate candidates.
Its observer covers initialization, level time, both RNG indices,
player position, momentum, angle, health, armor, ammo, weapon selection and
secret count, weapon/flash animation state, and selected imp/zombieman
state-machine, position, momentum and health fields, imp fireballs, and the normal
exit request. `scripts/compare-demo`
provides broader diagnostic traces against Chocolate Doom 3.1.1, including
map objects, impact effects and world state.

These are **differential test harnesses**, not equivalence proofs. The original
backend executes DOS DOOM.EXE in a pinned emulator; the diagnostic backend uses
Chocolate Doom as a compatibility proxy. Matching finite traces cannot prove
all-input equivalence. The arithmetic binary proofs retain their separate scope.

## Rendered frame comparison

`scripts/compare-render` compares Lean with the pinned Chocolate DOOM renderer.
This is a diagnostic proxy, **not a capture from the original DOS executable**.
Run it after fetching the shareware WAD and reference sources as described below:

```sh
./scripts/compare-render --ticks 1 777 950 1100 1242 1450 1881 --repeat
./scripts/compare-render --scenario sky-window --ticks 183 --repeat --out artifacts/render-sky-window
```

Each sample replays a normal input prefix from E1M1's player start. Before
comparing pixels, the harness requires all declared diagnostic gameplay fields
to match for the entire prefix and verifies the Lean renderer's final state.
This prevents a known simulation mismatch from being reported as a rendering
difference; it does not establish equality of unobserved state.

Both engines present once after the last tic: 320×200, high detail, a 320×168
world view plus status bar, original WAD RGB palette, and no host gamma, scaling
or aspect correction. Fuzz starts at phase zero. This profile does not reproduce
the display history of an interactive playthrough. Chocolate's renderer and HUD
routines run unchanged; instrumentation observes the palette and exports pixels.
`--repeat` checks fresh-process frame and state captures for byte equality.

The output includes `index.html`, PNG/PPM reference and Lean frames, a red pixel
difference mask, gameplay traces and JSON reports with source, executable, input
and output hashes. Every RGB difference counts; there is no perceptual threshold.
Exit **0** means exact frames, **1** means valid captures with visual differences,
and **2** means invalid evidence or a tool/input failure.

After the wall/plane, animated-surface, sprite and column-data passes, the seven
`e1m1-exit` samples give these counts (64,000 RGB pixels per frame):

| Tic | Before wall/plane port | Wall/plane pass | Surface/sprite pass | Column/phase pass |
| --- | ---: | ---: | ---: | ---: |
| 1 | 20,479 | 322 | 0 | 0 |
| 777 | 15,557 | 117 | 0 | 0 |
| 950 | 25,273 | 3,216 | 1 | 0 |
| 1100 | 17,891 | 136 | 0 | 0 |
| 1242 | 7,283 | 1,608 | 0 | 0 |
| 1450 | 16,740 | 1,293 | 0 | 0 |
| 1881 | 6,543 | 0 | 0 | 0 |

The independent 183-tic `sky-window` sample improves from 3,746 to 177 to **zero**
differing pixels. Every sampled 320×200 image, including its status bar, matches.
Repeated fresh-process frames and traces are byte-identical. These observations
do not establish equivalence for all frames or inputs. The comparison settings
and gameplay checks are unchanged. Final artifacts:
`artifacts/render-tightened-final` and `artifacts/render-tightened-sky-final`.
Previous evidence remains in `artifacts/render-sprites-final` and
`artifacts/render-sprites-sky-final`.

Changes include directory-based texture/flat animation with absolute-index phase,
fixed sprite transforms and rotations, original patch-origin and post rules,
wall silhouettes, masked-wall ordering, BSP bounding-box rejection, and fractional
weapon-post placement. The original texture loader's single-patch column path
ignores the patch placement's Y offset; preserving this fixes the SKY1 window views.

The final 178 differences had three causes:

- NUKE24's edge samples the trailing post padding byte, not the first texel after
  wrapping at its declared 24-pixel height. Opaque columns now retain the original
  WAD data pointer. Reads beyond the lump are safely absent, not host-memory reads.
- R_DrawColumnInCache shortens a post when its destination starts above the texture,
  but does not advance the source pointer. TEKWALL1 depends on this quirk.
- Passive map objects now use the already-recorded randomized first spawn countdown,
  followed by normal frame durations. This fixes the armor bonus's animation phase
  without consuming any additional random numbers or changing gameplay traces.

The tests compare 3,009 wall/plane arithmetic cases, 304 packed-span sequences,
4,590 sprite/post/animation cases, and 61 composite-column cases against extracted
C at `-O0` and `-O2`, plus the existing sky/light checks. Framebuffer regressions
exercise short-wall padding and passive-animation boundaries, partitioning and
restart. Runtime render-only effect insertion history, non-power-of-two texture
widths and overflow behavior remain outside a general pixel-equivalence claim.
None of these tests is a new universal proof or a comparison to original DOS video.

## Live pixel hunting

Run `./scripts/compare-live` and open the printed loopback URL. The first run
builds a separate pinned Chocolate worker and the persistent Lean worker. It uses
the local shareware WAD by default; `--wad PATH` selects another compatible E1M1
IWAD, `--port N` fixes the local port, and `--fetch` permits fetching the pinned
source archive if it is missing. Only one controlling browser window is intended.

Click **Play**. Matching RGB pixels are grayscale; **every differing pixel is
red**, with an exact count. The display menu (or Tab) switches to either engine's
unmodified color frame. WASD moves, arrows turn, Shift runs, Ctrl/left click fires,
Space uses, and 1/2/3 select weapons. P pauses, N advances one tic, B saves the
current frame pair, and R restarts both engines. Losing browser focus pauses input.
This is a silent E1M1 comparison; it stops at the exit request. Free camera and
intermission are outside this mode.

The controller constructs one vanilla-encodable ticcmd and sends those identical
four fields to both persistent processes. Each advances exactly one game tic and
returns its declared-state record and 320×200 RGB frame. Tick/command disagreement
or a worker failure stops advancement. The UI targets 35 tics per second; if the
host is slower, both engines slow together without dropping commands. The first
declared-state divergence stays visible even if later states reconverge: after
that point, red pixels may be caused by gameplay differences as well as rendering.

Live presentation occurs once per tic, retaining each engine's indexed screen, fuzz phase and
using Chocolate's normal incremental HUD refresh. This deliberately models frame
history, unlike the offline harness's one fresh presentation after a whole input
prefix. The raw palette, view dimensions and exact RGB comparison are unchanged.
The live adapter has its own source/build directory and provenance; it does not
modify `scripts/compare-render`, the offline observer, or its reference build.

**Save this frame** writes reference/Lean PNGs and PPMs, a difference mask, final
state records, source/binary/WAD hashes, `commands.txt`, and an original-format
`input.lmp` to the displayed folder under `artifacts/live-compare`. All commands
are also appended to the session's `commands.txt` while playing. Reproduce the
full presentation history with:

```sh
./scripts/compare-live --replay artifacts/live-compare/RUN/capture-TIC/commands.txt
# Or save a fresh final comparison without opening a server:
./scripts/compare-live --check --replay path/to/commands.txt
```

The replay opens paused at its final frame and can then continue interactively.
Restart creates fresh processes, preserving previous runs and captures.

`./scripts/test-live-comparison` checks declared-state synchronization throughout
the 1,881-tic exit route and 183-tic window-room route, saved replay output, and a
fresh-process window-room repeat. All these live checkpoints now match exactly.
The exit route previously retained five status-bar differences after a shotgun
pickup; the incremental widget fix below removes them. Other manually observed
world-pixel differences remain useful follow-up cases, not a claim of full correspondence.

A subsequent 6,793-tic manual recording exposed three runtime issues: importing
crossing/lighting state overwrote the landing sound's miscellaneous RNG draw
(first divergence at tic 944), the combat sprite loop overwrote living barrels'
randomized spawn phase, and dropped clips lost the victim's fractional XY.
Landing sound now follows the state import, living barrels retain their spawn
countdown, and drops use the victim's exact fixed XY with `ONFLOORZ`, including
collision links and rendering. The clip fix also removes an early pickup at tic
1542; it is not merely a visual adjustment.

After these changes the declared fields match at every tic in that recording.
All 6,793 status-bar images match exactly; 6,561 complete frames match exactly.
The other 232 frames still differ in the world/weapon region, with a maximum of
2,253 pixels. Local per-frame results and preserved commands are in
`artifacts/live-sprite-fixes/all-frames.json` and `user-commands.txt`. These are
finite replay results against the unchanged Chocolate worker, not a universal
rendering-equivalence proof. Regression fixtures cover landing pitch RNG,
barrel spawn/death rendering, and fractional drop positions and links.

The recorded slime-trail inspection adds a presentation-history regression at
tic 2964 (`tests/reference/slime-edge-commands.json`, run-length-encoded inputs).
The original renderer leaves a 38-pixel column unpainted at that view. A fresh
presentation matches, but clearing Lean's screen every frame erased pixels that
Chocolate retained from preceding frames. Both the native viewer and persistent
comparison worker now carry the indexed screen between presentations; the
current palette is applied to retained indices too. The captured column and its
whole frame now match exactly, preserving the artifact rather than altering BSP
geometry. `./scripts/test-live-comparison` replays the complete input history and
asserts exact final pixels and matching declared gameplay fields throughout.
Single-frame exports still begin with a fresh screen.

The 4,739-tic `fireball-barrels-commands.json` recording exercises a fireball
impact at a door and repeated barrel damage/explosions. At tic 3799, map-spawn
lighting and the missile explosion both used `P_Random`: their reversed update
order gave Lean a five-tic explosion countdown where Chocolate had four, despite
matching final RNG indices. Map-spawn lighting now runs after map actors and
before the dynamically spawned missiles. This is a correction of that ordering
relationship, not a complete general thinker scheduler.

Barrels already had matching fixed-point collision/momentum positions, but the
renderer only read precise runtime positions for actors with an AI brain. It now
uses synchronized runtime coordinates for all combat actors, including barrels
and their death sprites. The recording's declared state matches throughout;
impact and barrel checkpoints at tics 3799, 3803, 3944, 3957, 4119, and 4151 match
all pixels. Tic 4166 initially improved from 1,930 differences to one floor-edge
pixel at (307,141). The column-data corrections below remove that last pixel;
tic 4166 is now also an exact-frame checkpoint.
The final tic 4739 also matches exactly. The live integration test checks this
input history and these exact-frame checkpoints against the unchanged reference.

The `pixel-edges-commands.json` regression preserves another 1,079-tic living-player
input prefix. Every presented frame and every declared diagnostic state field
matches Chocolate throughout, with no pixel tolerance. It covers the opening
stairs, masked wall edges, and a monster opening a door at tic 933.

The stair fix retains the original packed composite-column cache: a sample just
past a short column can read the next cached column, skipping single-patch
columns that live in WAD lumps. Masked walls and sprites now sample their raw
patch posts, including trailing padding when fixed-point rounding selects it.
Post pointers advance even when a post is completely clipped. Buffer accesses
remain bounds checked; this does not reproduce arbitrary out-of-allocation reads.
A separate integration fix preserves the miscellaneous RNG stream advanced by
monster door-opening sounds when AI returns its gameplay RNG stream.

The full recording continues for 1,338 tics. Its former death divergence at
tics 1080–1081 is now covered by the player-death regression below. The original
1,079-tic rendering fixture remains unchanged. These results are differential
tests, not an all-input rendering or whole-game proof.

The 5,496-tic `door-projectile-hud-commands.json` recording closes a door onto
an imp fireball and later picks up the shotgun. Its first pre-fix state mismatch
was the projectile ceiling at tic 2678: Chocolate used 34 map units, Lean still
used 36. Doors and missiles now receive a shared allocation serial and tick in
that order, rather than all missiles preceding all doors. This preserves both
possible creation orders. Imp fireballs have `MF_NOBLOCKMAP`; they are not
height-clipped by the door's sector traversal. They observe new plane heights
on their own movement query. General ordering with floors and other dynamically
spawned actor kinds remains outside this scheduler subset.

The five HUD pixels were the transparent edge of the shotgun's arms digit.
`STlib_updateMultIcon` restores the old icon rectangle from `STBAR`, then draws
the new digit. It does not redraw the `STARMS` background. Lean now retains widget
history alongside framebuffer history: numbers redraw each presentation,
percents and STARMS draw on full refresh, and changed multi-icons restore their
old rectangle. Standalone exports and viewer restart still request a fresh bar.

After both fixes, all declared state fields and every status-bar frame match
for all 5,496 tics. Of the complete frames, 5,473 are byte-identical; 23 retain
unrelated world/weapon differences (at most 32 pixels). The regression requires
exact HUD pixels throughout plus exact full frames at the door/shotgun
checkpoints. It does not mask world differences in the live viewer.

The `player-death-commands.json` replay extends the stair/masked-edge recording
through a lethal attack at tic 1080 and 258 more tics. The old adapter hid the
weapon and lowered a floating-point camera immediately on the killing tic;
it then froze the body and never turned toward the killer. The new dead-player
path runs psprites first, lowers the fixed-point view height toward six units,
uses the original dead `P_CalcHeight` branch, turns by the integer `ANG90/18`
step toward the attacker's current fixed-point position, and fades damage flash
only in the original strict angular interval (or when there is no attacker).
The player mobj then retains collision/sliding, friction and vertical motion,
including the corpse-on-a-ledge friction exception, before its death state clock.
Weapon patches continue to render while their original psprite state lowers them.
No death-view update runs early on an enemy-caused killing tic.

All observed gameplay fields match through all 1,338 tics. Exactly 1,337 complete
frames match; tic 1081 retains four world pixels behind the imp, with an exact
HUD. That difference stays visible and is captured without a tolerance. A second
1,380-tic replay holds movement, turning, firing and weapon-selection inputs
after the same death to check the dead-player path. The kernel test compares
2,475 view/angle/flash cases with unchanged `P_DeathThink` and `P_CalcHeight`
bodies at `-O0` and `-O2`; its weapon routine is a counted stub and its target
angle is injected, while the full replay exercises actual psprites and attacker
geometry. These are reference tests, not new formal proofs. The original
BT_USE → PST_REBORN → level-reload lifecycle remains separate work; the existing
viewer/comparison Restart action continues to work.

### Stray pixels and reference memory layout

The `stray-memory-commands.json` recording contains 4,097 tics with matching
observed gameplay fields and HUDs. Ten frames differ, totaling 18 pixel instances
(one to five in any frame). Tracing the first differing pixel in each frame
shows the same integer sample coordinates in both renderers, followed by a read
outside the complete composite texture cache or patch lump. Lean's bounded
`ByteArray` lookup returns `none`, retaining the underlying pixel. The native
Chocolate build reads adjacent zone-allocation bytes as palette indices.

| Tic | Texture/lump | Buffer bytes | Read offset | Reference byte |
| --- | --- | ---: | ---: | ---: |
| 112, 141 | STEP6 composite | 512 | 512 | 40 |
| 481 | STEP6 composite | 512 | 607 | 103 |
| 1183 | BON1B0 | 292 | 353 | 0 |
| 1190 | BON1A0 | 292 | 353 | 0 |
| 2086 | TROOD4D6 | 1012 | 1101 | 1 |
| 2108 | PLAYW0 | 1364 | 1451 | 0 |
| 2337 | BAL1C0 | 1316 | 1342 | 29 |
| 2351 | COLUA0 | 832 | 915 | 0 |
| 3932 | CBRAA0 | 1100 | 1213 | 1 |

The STEP6 boundary reads the low byte of the next zone block's size, 8,232:
`8232 & 255 = 40`. In several other cases, a tiny negative starting texture
fraction rounds to -1; the original `& 127` row mask selects row 127 beyond the
short patch. This includes decoration pixels beside the spectre at tic 3932;
the traced mismatch is not the fuzz kernel.

A separate diagnostic build adds eight zeroed bytes after every zone allocation.
With the renderer, WAD and input unchanged, the reference pixels at tics 112 and
141 turn from dark red to black. This establishes dependence on allocation
layout. It is not a proposed renderer fix, and the normal comparison reference
was not modified. Raw traces, captures, build provenance and the controlled
experiment are in `artifacts/stray-pixels/audit.json` and adjacent files.

Matching these bytes would require an explicit reference memory-layout model;
the 64-bit native Chocolate zone layout is not the original DOS layout. The
comparison continues to show every differing pixel. No byte values are
hard-coded and no tolerance or masking is introduced.

The audit also found an independent Lean bounds warning at tic 3303: an
untextured portal evaluated tangent index 4097 in a 4096-entry table. Texture
coordinates are now evaluated only when texture data is used, avoiding that
unused lookup. The saved replay checks exact gameplay/HUD correspondence, exact
frames including tic 3303, captures the ten remaining differences, and rejects
bounds panics in the Lean log. This fix does not remove the memory-dependent
pixel differences above.

## Live original DOS rendering

```sh
./scripts/compare-original-live
# Equivalent shared launcher:
./scripts/compare-live --reference dos --out artifacts/dos-live-compare
# Replay a saved live input sequence:
./scripts/compare-original-live --replay /path/to/commands.txt
./scripts/test-original-live-comparison
```

The browser offers the same controls, grayscale/red difference view, pause,
step and capture buttons. Its reference is the hash-pinned, unchanged shareware
1.9 `DOOM.EXE` in a separate DOSBox-X build. `compare-live` without `--reference`
continues to select Chocolate; existing Chocolate sessions remain available.

The live adapter supplies exactly four pending demo bytes immediately before
DOS `G_Ticker`'s inlined demo reader at code offset `0x20607`. The executable's
own instructions decode those bytes and advance the demo pointer. The adapter
does not modify instructions, registers, allocator data, simulation state or
renderer state. This is explicitly an emulator input adapter, not a wholly
read-only run. The older offline DOS observer remains read-only and unchanged.
The on-disk demo has a fixed 10,000-command capacity; restart after that limit
(about 4 minutes 46 seconds). Only the dedicated game-input directory is mounted.

DOS renders directly into unchained VGA memory. At `0x1d4a2`, after the original
`D_Display` drawing and before page flipping or a screen wipe, the adapter reads
the current 320×200 Mode X page from DOSBox's four interleaved planes. It pairs
that image with the state observed after the same game tic. Every input, state
and frame must occur in sequence; unexpected pointers, pages, mappings and
palette state stop the capture. File bytes and data relocations for the input,
palette, presentation and page-flip instructions are pinned in
`tests/reference/original-live.json` and checked before launch.

Pixel comparisons use the original palette supplied to `I_SetPalette`, before
VGA's six-bit DAC conversion, with gamma zero. This measures exact logical
rendered RGB, without CRT effects, scaling or host screenshot artifacts. It is
not a comparison of physical display signals. Wipes, menus, intermission and
audio output are outside this live view. Gameplay comparison uses the declared
DOS v6 fields described below, which are fewer than the Chocolate diagnostic
fields; matching them is not a whole-state equivalence proof.

The original opening melt initializes 320 columns through `M_Random`. The
Lean worker's explicit `--dos-presentation` mode runs `Wipe.initialDelays`
after its first captured frame, before the next tic. This models the actual
initialization algorithm, including column delays and wrapping RNG; it does
not overwrite Lean's RNG with an observed reference value. The ordinary
Chocolate worker mode does not run that transition. Melt instruction evidence
is included in the live profile.

The exit route also exposes a grazing wall projection at tic 2018 whose tangent
index is 4100, beyond the nominal 4096-entry table. In the pinned DOS executable,
`finetangent` starts at data-object offset `0x1a84` and `finesine` follows at
`0x5a84`. Lean now explicitly reads this adjacent sine region instead of panicking.
`test_original_render_tables.py` checks the LE page mapping, absence of loader
fixups, all 8,192 reachable table values and the compiled Lean lookup against
the original executable. This reproduces a fixed executable layout; it does not
model the variable zone-heap reads described above.

Before the heap integration below, the 4,097-tic `stray-memory` recording
matched all compared gameplay fields and all HUD pixels against DOS, with
eleven differing frames totaling 31 pixel instances. The same stair samples have different colors in DOS and native
Chocolate, consistent with their different surrounding allocation contents.
An additional DOS difference appeared at tic 1455. These were recorded as
findings, without pixel tolerances or masks. The first investigation is retained in `artifacts/dos-live/replay-report.json`.

The integration test covers movement, firing, moving fire, an enemy encounter,
the E1M1 exit, the door/projectile recording, death inputs, and the stray-pixel
recording. It checks state/HUD equality, records world-pixel discrepancies,
requires exact movement frames, repeats movement in fresh emulator processes,
and checks that one-bit state and pixel mutations are detected. Captures retain
the original state trace, runtime address bindings, exact commands, both
images and differences. Provenance includes the DOS executable, emulator
source/build/adapter, Lean executable, WAD and configuration hashes. These
finite checks and executable bindings are evidence, not a verified emulator
or a formal rendering-equivalence theorem.

### Diagnosis of the former 37 differences in the 2,211-tic DOS runthrough

The later manual E1M1 recording (command-file SHA-256
`5ba9eea686591c3cd44527c6b2655d599ea8c54acf73231a2889b3e0d86e3e2e`)
initially had 2,200 exact frames and 37 differing pixel instances across 11 frames.
All compared gameplay fields and every HUD pixel match throughout. A separate
diagnostic replay traces **each of the 37 pixels**, rather than only the first
difference in a frame.

The emulator observer records the original column drawer's inputs at code-object
offset `0x1bd28`, its actual assembly writes at `0x1be00`, `0x1be0d` and
`0x1be3b`, and the surrounding zone allocation. A diagnostic Lean worker records
the corresponding texture fractions, row indices, source offsets, samples and
pixel writes. These observers do not change texture data or guest allocations.
The final differing write at every coordinate reads outside the complete texture
buffer in DOS; Lean calculates the same fraction, step, row and source offset,
then its bounded lookup returns `none` and leaves the underlying pixel intact.

| Tic | Pixel instances | Texture or patch lump | Buffer bytes | Read offsets from buffer start |
| ---: | ---: | --- | ---: | --- |
| 102 | 2 | STEP6 composite | 512 | 512 |
| 456 | 5 | POSSA2A8, walking zombieman | 1316 | 1395 |
| 476 | 14 | CLIPA0, ammo clip | 188 | 189, 205, 221, 237, 253, 269, 285 |
| 495 | 1 | POSSK0, dying zombieman | 1128 | 1225 |
| 506 | 5 | POSSL0, corpse | 988 | 1091, 1100, 1110 |
| 540 | 1 | STEP04, stair patch | 552 | 604 |
| 582 | 2 | POSSL0, corpse | 988 | 998, 1036 |
| 856 | 1 | COLUA0, decoration | 832 | 882 |
| 1396 | 3 | COLUA0 | 832 | 935, 944 |
| 1419 | 1 | COLUA0 | 832 | 910 |
| 1505 | 2 | MEDIA0, medikit | 780 | 889 |

At tic 476, the clip's starting fixed-point fraction is `-4`, or `-4/65536`
texel. Arithmetic right shift followed by the original `& 127` selects row 127
for an 11-pixel-high sprite. Reads beyond its 188-byte patch produce bytes 0,
190 and 164; light-map row 13 turns them into palette indices 0, 47 and 74.
The reference writes these over an already-drawn corpse. Both renderers agree
on the sample arithmetic; the difference is what memory exists beyond the patch.

The two STEP6 pixels read exactly at the end of its 512-byte composite. This is
the first byte of the next DOS zone block's size: `8216 & 255 = 24`. That becomes
palette index 24, producing RGB `(203, 107, 107)` in the captured frame. The full
512-byte allocation was matched to a reconstruction of STEP6 from the WAD;
patch identities above were checked against every byte of their WAD lumps.

Validation reproduced all 11 differing frame pairs plus the final frame pair
byte-for-byte, with an identical full DOS state trace. Every recorded source
byte maps through COLORMAP to the actual assembly write and a PLAYPAL RGB value
matching the saved pixel. Evidence, diagnostic source/build provenance and the
verification script are retained locally in `artifacts/dos-pixel-trace/`, with
per-pixel records in `pixel-traces.json` and checks in `verification.json`.
The normal Lean renderer was restored and rebuilt after diagnosis; the running
comparison servers and normal DOS reference were unchanged.

This accounts for all differences in this recording, not every possible input.
That diagnostic stage did not fix rendering or add a formal theorem. The live
integration below reproduces the reads using a DOS memory model, allocation/cache
ordering and neighboring WAD bytes. It does not use hard-coded colors or masks.

### DOS heap model and live allocation lifecycle

`Doom/DosMemory.lean` now models a 32-bit address space and the original zone
allocator in safe Lean. Block headers, pointer cells, payloads and retained freed
bytes occupy the same modeled memory. It ports `Z_ClearZone`, `Z_Malloc`,
`Z_Free`, `Z_FreeTags` and `Z_ChangeTag2`, including four-byte alignment, 24-byte
block headers, the strict `extra > 64` split boundary, rover search/coalescing,
cache purging, owner-pointer clearing and the sentinel value 2. A block's `user`
field determines whether it is free; a zero tag alone does not. New free headers
retain the original routine's unwritten bytes, rather than zeroing them.

Unmapped and uninitialized bytes remain unknown. The model never invents zero
for them. Explicit byte writes and WAD copies mark their destinations known;
freeing a block preserves those bytes. `DosCache.lean` adds WAD cache ownership,
tag changes on hits, copying on misses and reload after purging. The cache pointer
array is supplied from the separate DOS C-runtime address space, as in the
original; it is not allocated inside the zone.

`ColumnSource` can now bind a backing buffer to a guest address. Wall and sprite
sampling consult the current `Art.dosMemory` when bound. An 11-high sprite test
exercises the real drawer with fraction `-4`, verifies its row-127 overread,
and changes the neighboring byte to verify that the actual output pixel follows
memory. Unbound artwork retains the existing bounded lookup.

The independent allocator oracle executes the hash-checked original x86 routines
under Unicorn. `tests/reference/original-zone.json` pins the routine ranges,
hashes and mainzone relocation; the test rejects execution outside those routines
except the original error entry. Thirty scenarios cover alignment, the split
threshold, both coalescing directions, rover repair, purging, tag ranges, owner
sentinels, invalid operations and deterministic randomized sequences. Successful
operations compare every zone and owner-region byte, including stale payloads;
fatal errors compare rejection only. This is differential testing, not a new
formal equivalence theorem. The allocator accepts nonnegative allocation sizes
within its documented supported range and rejects corrupt walks with a fuel
limit.

Build and run the checks (Unicorn setup is shared with `docs/BINARY_PROOF.md`):

```sh
./scripts/lake build dos-memory-probe
/tmp/leandoom-binary-tools/bin/python scripts/verify_original_zone.py --out artifacts/dos-zone-check
python3 -m unittest discover -s tests -p test_dos_memory.py -v
```

A separate read-only DOS diagnostic records the allocator calls from the same
2,211-tic playthrough. Replaying those calls in Lean matches all **1,545 allocation
addresses**: 1,362 during startup and 183 during play. WAD loads fill their modeled
allocations; unrelated payloads remain unknown. All **37 recorded overread bytes**
then follow from the generated headers and cached WAD data. The clip's neighbor
is SHELA0 (shells); other neighbors include POSSA3A7, POSSL0, POSSM0, STEP03,
BPAKA0 and ARM1A0. No observed pixel colors are written into the model.

The recorded-call check can be reproduced with the locally retained trace:

```sh
python3 scripts/replay_original_zone.py \
  --trace artifacts/dos-zone-trace/replay/run-1791492038917972000/zone-calls.jsonl \
  --lump-cells 0xa8f024 --out artifacts/dos-zone-replay \
  --overreads tests/reference/dos-texture-overreads.json
```

The live DOS profile now generates its own requests. `DosStartup.lean` ports the
original startup order from WAD metadata and the DOS ABI: texture lookup arrays,
patches, sprite lumps in directory order, sprite frames, HUD, map records and map
thinkers. `DosHeap.lean` owns the cache and composite resources. Rendering requests
columns and flats in drawing order; gameplay requests objects, doors, movers and
PC-speaker sound lumps (the original still caches these with `-nosound`).
`P_RemoveThinker` defers frees until the next thinker visit. Opening-wipe scratch
allocations occur after the first captured frame.

For the saved **2,211-tic run**, the independently generated sequence matches all
**1,467 allocations and 79 frees** through the final E1M1 presentation: sizes,
tags, owner cells and returned/freed addresses. This includes all **1,362 startup
allocations**. The 78 later allocations in the diagnostic trace belong to
`WI_Start`, after the captured exit frame; intermission remains outside the live
adapter's scope. The complete replay against DOS has **2,211 exact RGB frames,
zero differing pixels, and no differences in the declared gameplay fields**.
All 37 former texture-overread pixels now come from generated allocator headers
or neighboring WAD payloads. This is finite differential evidence, not a theorem
for every playthrough or the entire game.

After heap integration, before the video-page fix below, the broader eight-case
DOS suite covered 14,395 tics (plus a fresh 141-tic movement repeat). All declared
gameplay fields and HUD pixels matched. Remaining world-image differences were
exit-route tics 942/2018, door/projectile tics 2144/2207/2217/4247, and the older
stray-memory route at tic 1455: seven frames, down from 48. These were retained
as visible findings.
The complete runthrough and before/after integration reports are retained in
`artifacts/dos-heap-live/`; no regression tolerance was added.

The model is deliberately scoped to the pinned shareware WAD, 8 MiB zone, silent
DOSBox profile and 10,000-tic transport buffer. `DosHeap.Layout` declares the DOS
process-layout inputs (zone base `0x28e024`, cache cells `0xa8f024`); they are not
inferred from each frame. A different DOS environment requires validating its
layout. Only initialized allocator/resource bytes are authoritative. Unmodeled
object and scratch writes invalidate their known-byte coverage; encountering an
unknown bound texel stops the comparison with an error instead of silently
painting a fallback color. This is not a complete memory image of every C struct.

`tests/reference/dos-heap-commands.json` records input commands, DOS output hashes
and provenance for regressions. Startup and live probes receive only the WAD and
ordinary controls; neither that fixture nor the recorded allocator calls are
read by the engine. `LEANDOOM_HEAP_TRACE` optionally writes generated allocation
requests for diagnostics. The existing neighborhood fixture and recorded-call
replayer remain separate kernel checks.

```sh
./scripts/lake build dos-startup-probe live-render-probe
python3 -m unittest discover -s tests -p test_dos_heap.py -v
./scripts/test-original-live-comparison
```

The ordinary Chocolate comparison keeps bounded resource buffers. No tolerance,
mask, recorded color, or reference memory is applied to either comparison.

### DOS video page history at slime-trail seams

A subsequent 1,941-tic manual run (input SHA-256
`eee50b326127b6286660b8ecd011c087d07924f8183403e6cf13b9ae6b635f97`)
exposed 131 differing pixels across nine frames at the seam before the zigzag
room: tics 1390, 1397, 1583, 1614, 1642, 1677, 1678, 1769 and 1772. All declared
gameplay fields and HUD pixels already matched. These were retained image
contents, not additional texture-buffer overreads.

Original DOS draws directly into three Mode X video pages. The pinned
`I_FinishUpdate` instructions at `0x19fca` advance the page by `0x4000` and wrap
at `0xc000`. When BSP rounding leaves a column unpainted, the pixels on that
page survive from three presentations earlier. Lean had retained the immediately
preceding image, as appropriate for the software-buffer Chocolate comparison.
For example, all 26 mismatches at tic 1397 match the pixels from tic 1394;
none match the preceding frame. A gap can also survive multiple page rotations.

`Doom/DosVideo.lean` gives the DOS worker three independent indexed viewports.
Before drawing, it restores the next page's viewport; after drawing, it stores
that page and advances the cursor. Heap state, fuzz phase and status/widget state
continue from the latest presentation. Palette indices, rather than historical
RGB colors, ensure retained pixels use the current palette. The normal renderer
and Chocolate comparison continue to use their existing single-buffer history.

A separate read-only DOSBox diagnostic confirmed the real VGA page cycle and
that all three viewports contain the completed first image after the opening
melt. It also confirmed that frame 5 reuses frame 2's unmodified viewport.
Observer source, snapshot hashes and results are in
`artifacts/dos-slime-latest/pages-report.json`; no reference image or page bytes
are supplied to the Lean worker.

Replaying the complete manual run after this change gives **1,941 exact RGB
frames, zero differing pixels, matching declared gameplay fields and an identical
DOS state trace**. Rechecking the earlier eight routes leaves three differing
frames: exit-route tics 942/2018 and door/projectile tic 4247. The other three
door/projectile differences and the older stray-memory tic 1455 also disappear.
All declared gameplay fields and HUD pixels continue to match. The 494 Python
tests and 98 Lean checks pass. Five of those Lean checks exercise page rotation, repeated unpainted
gaps and status-bar preservation. `tests/test_dos_video.py` independently replays
the controls and compares full-frame DOS hashes at all nine former mismatch
frames and the final frame. The DOS integration suite also replays this route
and requires every frame to match exactly. This remains evidence for the recorded inputs and
pinned presentation profile, not a whole-game equivalence theorem.

## Original executable backend

On macOS, install SDL2, CMake, autoconf, automake and libtool, with a C/C++ compiler
and Python 3.12+. The DOSBox-X source build also uses host platform libraries;
other host configurations have not yet been validated. The first build takes
several minutes. Shareware game files stay local and are never committed.

```sh
./scripts/fetch-shareware
./scripts/compare-original-demo --fetch --scenario movement --out artifacts/original-movement
./scripts/compare-original-demo --scenario combat --out artifacts/original-combat
./scripts/compare-original-demo --scenario moving-combat --out artifacts/original-moving-combat
./scripts/compare-original-demo --scenario enemy-encounter --ticks 1000 --out artifacts/original-enemy-encounter
./scripts/compare-original-demo --scenario shotgun-secret --ticks 2500 --out artifacts/original-shotgun-secret
./scripts/compare-original-demo --scenario e1m1-exit --ticks 2500 --out artifacts/original-e1m1-exit
./scripts/compare-original-demo --demo /path/to/e1m1.lmp --ticks 1000
./scripts/test-original-demo-comparison
```

Exit codes are 0 for a match in both comparisons, 1 for any divergence, and 2 for
invalid/incomplete evidence or a tooling error. Inspect `comparisons.lean` and
`comparisons.chocolate` separately. A disagreement with Chocolate is not resolved
by substituting its values for the original's values. `--fetch` allows only
missing, hash-pinned source downloads; subsequent runs can be offline.

The DOSBox-X source commit is
`e013b8bf8e27ef878a646049bf5b2e732878d616`; the archive hash, instruction evidence,
relocations, and field layout are in `tests/reference/original-tick.json`.
DOOM.EXE SHA-256 is
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
The executable comes from the same verified shareware archive as the existing
arithmetic proof extraction. No source rebuild or patch of DOOM is involved.

The observer is inserted in DOSBox-X's normal CPU interpreter, before instruction
execution. The DOS profile uses a 486, 32 MiB RAM, fixed 30,000 cycles, no drawing,
and no sound. Only a dedicated directory containing game inputs is mounted.
The observer reads guest RAM without changing guest registers, flags, code or
data, then ends the host process after the requested final snapshot. It records
the input command before gameplay can modify it.

The first boundary is the call to `P_Ticker` at code-object offset `0x2081a`.
The post-tick boundary is `0x2082e`, after `P_Ticker`, `ST_Ticker`, `AM_Ticker`
and `HU_Ticker`. The unique 22-byte call sequence is checked against the original
file and against running memory. File inspection checks that the sequence has no
loader fixups. The hook derives the actual code base at runtime, then derives the
data base independently from five relocated operands: two RNG indices, paused
state, the player table, and level time. All five must agree. The file's LE fixup
records must identify the expected targets in data object 3.

The profile also records instruction bytes from `P_Ticker`, `P_MovePlayer` and
`P_PlayerThink`, documenting the reverse-engineered player/command layout. The
observer checks alternating before/after boundaries, level time against observed
tic count, RNG bounds, an unchanged data segment and a plausible player pointer.
Paging is outside this validated profile. Address binding evidence is saved in
`binding.json`. These are consistency checks on an externally derived layout,
not a formal proof of that layout or of the emulator's x86 implementation.

The enemy observer additionally binds the thinker sentinel and state table from
relocated data operands, and `P_MobjThinker` from a relocated code operand. It
walks the live thinker list read-only and identifies the six E1M1 enemies by
their pinned spawnpoint tuples. Duplicate, missing initial, or unknown identities
fail validation. State pointers must address one of the 967 original 28-byte
state records. Captured offsets have instruction-byte evidence whose encoded
displacements are checked against the declared layout. Targets in this DOS
profile may be null, the player, or one of those six enemies; other targets fail
explicitly. The profile excludes respawning and general spawned-enemy identity.

The original trace has its own smaller schema, `leandoom-original-tic-trace-v6`.
The two diagnostic traces are explicitly projected onto its declared player,
weapon, RNG, level-time, `enemyBrains`, `projectiles` and `exitRequested` fields; missing fields are never
filled with defaults. All commands and record counts must match before a
behavioral report is accepted. Fixed-point values are compared as exact signed
32-bit integers and angles as unsigned 32-bit integers, with no tolerance.

`report.json` contains both comparisons, their first divergent ticks and values,
and the first difference in each field. `provenance.json` records source, observer,
builder, binary, input, config and trace hashes, plus runtime address bindings.
`diagnostic/` retains the broader Chocolate-versus-Lean report and complete traces.
The emulator build cache is accepted only when the source archive, observer,
builder, profile and executable hashes agree with its local build record.
`--rebuild` forces fresh extraction and compilation; cached source edits are
never incrementally compiled. This bookkeeping is not a signed build attestation.

The integration check runs movement (141 tics), pistol firing/use (170 tics),
moving pistol fire (145 tics), the first enemy encounter (521 tics), and the
shotgun-secret route (1,961 tics), and the exit route (2,445 tics),
repeats the original in fresh emulator processes, and injects a one-bit position
change at tic 42 to verify detection. It requires Chocolate to agree with the
original on these pinned cases. It also requires Lean to match all six
complete cases, including the broader Chocolate diagnostic fields. Initialization
and all 141 movement / 170 firing-use / 145 moving-fire tics currently match.
The encounter now matches all 521 tics of both profiles, including enemy motion
in DOS memory. Additional mutations change enemy 87's countdown, X position,
horizontal/vertical momentum or health by one bit at tic 42 and must identify
that exact field. The longer route additionally checks RNG mutations at the
slime-damage and shotgun-firing boundaries. Health loss, secret discovery,
weapon selection and shell consumption are now checked directly in DOS memory.
Mutations change health, armor, pending weapon, shells, weapon/flash states and
countdowns, refire and extra light, and must identify the exact field and tic.
Medikit removal and floor lowering still use the diagnostic profile; impact
objects are not yet captured from DOS. Version 5 adds imp fireballs, including
their explosion states, as described below.

### Player and weapon memory layout

Version 4 reads player health, armor points/type, the four ammo counters,
ready/pending weapons and secret count. It also captures weapon state/countdown,
raw weapon XY, muzzle-flash state/countdown, refire and extra light. The observer
checks the player mobj's backlink to the same player structure. Weapon/flash
state pointers must be null or aligned entries in the original 967-state table;
that table is independently bound from `P_SetPsprite`'s relocated operand.

`original-tick.json` records exact original instruction bytes and encoded
displacements from `P_DamageMobj`, `P_PlayerThink`, `P_CheckAmmo`,
`P_PlayerInSpecialSector`, `P_SetPsprite`, `P_MovePsprites`, `A_ReFire` and
`A_Light1`. The two 16-byte psprites and their loop count are supported by
`P_MovePsprites`' increment/comparison instructions. Ammo is a four-element
array of 32-bit counters, indexed with scale four by the original code.
The profile, builder and observer are hashed with every capture.

DOS `wp_nochange` is **10**, verified from `P_BringUpWeapon`'s comparison and
assignment. Lean uses 9 internally. Both are serialized as `pendingWeapon: null`;
this is a representation mapping, not a gameplay change. DOS enum slot 9 is
rejected as an invalid weapon. A null psprite state becomes state number zero;
its stored countdown is still read, not replaced with a default.

Tests compile the actual observer against controlled guest RAM to check distinct
ammo/weapon values, null-state transitions, and rejection of misaligned/out-of-range
state pointers, invalid selections, inconsistent data binding and broken player
backlinks. Other tests reject missing old-schema fields and changed layout
offsets. These checks help validate the observer; they do not formally prove
the reverse-engineered layout or emulator correctness. Player powers, ownership,
max ammo and full damage bookkeeping are still outside this DOS schema.

### Imp fireball observations

Version 5 of both trace schemas requires a `projectiles` array. Each entry records
raw XYZ position and momentum, angle, floor and ceiling heights, state number,
state countdown, source identity, spawn `lastlook`, and the missile flag. Entries
follow live thinker order. Both observers select `MT_TROOPSHOT` by type, so an
explosion remains observable after DOOM clears its missile flag. Removed
thinkers disappear from the array. Lean preserves the same live creation order.

The DOS profile checks instruction-byte evidence for each captured field and
pins the original `A_TroopAttack`, `P_SpawnMissile` and `P_ExplodeMissile` code.
The projectile's `target` member holds its **source**, not its destination:
`P_SpawnMissile` stores the firing actor there. Sources in this profile may be
null, the player, or one of the six identified E1M1 enemies. Unknown source
pointers and invalid state pointers fail capture. The allowed fireball and
explosion states are 97–101.

The 1,961-tic route contains six fireballs from two imps and 414 projectile
snapshots. It covers flight from tic 777, an explosion at tic 857 and removal by
874; a fireball already exploding on its spawn tick at 1,242; and the second
imp's hit that leaves the player with two health at 1,633. All declared fields
match the original executable and Chocolate throughout the route. No physics
change was needed to obtain this match. Lean now retains `lastlook` from an
existing spawn RNG draw that it previously discarded; this adds no RNG draws.

Tests deliberately change every captured field or remove a shot and
require detection at the exact tic. Controlled-RAM tests run the actual DOS
observer against two simultaneous shots in thinker order, with one exploding,
then remove one and advance the other's explosion. The real route has at most
one live fireball at a time; concurrent gameplay is not established by that
synthetic decoder test.

These arrays do not assign persistent projectile identities across tics or
observe individual collisions within a tic. Other projectile types and general
dynamic thinker interleaving remain outside this profile. These are finite
comparison results, not a new universal proof of projectile equivalence.

## Broader Chocolate diagnostic backend

Install the same Lean/SDL2 prerequisites as the engine, plus Python 3.12+ and
CMake. SDL2_mixer and SDL2_net are not required. Fetch the shareware WAD once:

```sh
./scripts/fetch-shareware
./scripts/compare-demo run --fetch
```

`--fetch` permits downloading the pinned full reference source archive only if
missing. The archive and individual reference files are hash-checked. Subsequent
runs are offline and rebuild the reference from that checked archive. No game
assets or original executable are committed.

```sh
./scripts/compare-demo run --scenario idle --out artifacts/compare-idle
./scripts/compare-demo run --scenario movement --out artifacts/compare-movement
./scripts/compare-demo run --scenario combat --out artifacts/compare-combat
./scripts/compare-demo run --scenario moving-combat --out artifacts/compare-moving-combat
./scripts/compare-demo run --scenario enemy-encounter --ticks 1000 --out artifacts/compare-enemy-encounter
./scripts/compare-demo run --scenario shotgun-secret --ticks 2500 --out artifacts/compare-shotgun-secret
./scripts/compare-demo run --scenario e1m1-exit --ticks 2500 --out artifacts/compare-e1m1-exit
./scripts/compare-demo run --demo /path/to/e1m1.lmp --ticks 1000
```

The default movement scenario has 141 commands: idle, forward movement, turning,
an arbitrary combined forward/side/turn command, then coasting. The combat
scenario fires the pistol and uses a wall. The moving-combat scenario combines
forward/backward motion, strafing, turning, pistol fire and coasting in the
starting area. The 521-command enemy encounter walks to the first door, opens it,
approaches the zombiemen, waits for incoming fire, then fires the pistol. Request
`--ticks 1000` to include the entire scenario rather than the default 200-tic
prefix. The 1,961-command `shotgun-secret` route extends that exact prefix through
the remaining zombiemen, first imp, damaging slime, second door, hidden-floor
trigger, secret supplies and three shotgun blasts. Use `--ticks 2500` to include
the full route. The 2,445-command `e1m1-exit` scenario extends that exact prefix
through the remaining imp, corpse crushing, the last door and exit-switch use.
It also fits under `--ticks 2500`. These are generated command sequences
in the original demo format, **not recordings shipped with original DOOM**.
The shareware WAD's built-in demos are on other maps and are outside this first
E1M1 profile.

Exit status is deliberately meaningful:

- **0:** initialization and all requested tics match for the declared fields.
- **1:** a behavioral/state divergence was found; inspect `report.json`.
- **2:** invalid/unsupported input, incomplete evidence, or a build/runtime error.

All six pinned regression scenarios match their declared fields. Wider gameplay
can still diverge; exit 1 must not be relabeled a passing parity check.

## First supported profile

- Vanilla 1.9, version byte 109; four-byte single-player commands.
- E1M1 on the hash-pinned shareware 1.9 WAD; Hurt Me Plenty (skill byte 2).
- Player 1 only; default deathmatch/fast/respawn/nomonsters flags.
- Ordinary movement, attack, use, and fist/pistol/shotgun selection.
- Up to 10,000 commands; `--ticks` defaults to 200 and selects a prefix.

Other headers, longtics, pause/save commands, unsupported weapon selections,
truncated commands, missing terminators, and nonzero trailing payloads are errors.
The full supplied demo is validated even when only a prefix is executed. Zero
padding after the terminator is accepted. A normal exit request is supported on
the final requested tic. Continuing into `G_DoCompleted` or intermission is an
explicit unsupported runtime boundary, never a successful truncated match.

Demo movement bytes are signed. The angle byte becomes a signed 16-bit turn by
multiplying by 256. Lean receives those commands **directly**, without converting
them to keyboard presses, rounding them, or applying keyboard turn acceleration.
`Simulation.tickCommand` invokes the same simulation/combat code as the viewer;
the viewer's existing keyboard path remains the default.

## Trace boundaries and representation

Record 0 is the initialized map immediately before its first `P_Ticker` call;
its command is null. Record N is after N commands. The reference observes after
`P_Ticker`, `ST_Ticker`, `AM_Ticker`, and `HU_Ticker`, including the status bar's
miscellaneous RNG draw. No renderer runs. Record N carries command N−1 from the
decoded demo. Both streams must have exactly the requested length and identical
commands before any behavioral comparison is accepted.

Each record has `tick`, `command`, and `state`. Fixed-point fields are signed
raw 16.16 integers; angles are unsigned binary-angle integers. No floating-point
tolerance, rounding, or state resynchronization is applied. The only enum
normalization is `pendingWeapon: null` for no change (C sentinel 10, Lean 9).

The compared state includes:

- Player position, momentum, angle, floor/ceiling, view values, health, armor,
  ammo, ready/pending weapon, and secrets.
- Weapon/flash state numbers and tics, weapon offsets, refire and extra light.
- Both random indices and level time.
- Sector floor, ceiling, light and special; linedef specials; side X offsets.
- Original map actors' editor types, positions (including `z`), health, and presence.
- Imp/zombieman state number, countdown, angle, chase direction/count,
  reaction time, target threshold, lastlook, target identity and behavior flags.
- Imp/zombieman raw XYZ position, XYZ momentum and signed health, including corpses.
- Live puff/blood effects in thinker order: raw position, vertical momentum,
  floor/ceiling, state, countdown and lastlook.
- The level-exit request.

Sector/line/side arrays preserve WAD order. Actor dictionary keys are original
THINGS indices, so two identical objects at the same coordinates remain distinct.
The C observer tracks original map spawns and removals without changing actors.
The Lean exporter uses the same pure scene synchronization as gameplay queries:
prototype enemies own integer map positions, while imps and zombiemen retain precise scene
positions. Snapshotting never commits that projected scene to the simulation.

Schema `leandoom-tic-trace-v5` retains the `impacts` array added in v2. The reference walks the
existing thinker list read-only, selecting live puff/blood objects; it neither
reorders nor updates them. It adds `enemyBrains`, keyed by original THINGS index.
Target identity is -1 for null, 0 for the player, or the target's THINGS index + 1.
`behaviorFlags` contains only ambush, just-hit and just-attacked bits (mask 224).
Version 4 adds the seven motion/health fields to every enemy entry. Version 5
adds the imp-fireball `projectiles` array described above. Old traces missing
any required collection or field fail validation.

Full actor state machines, general thinker order, other runtime-spawned objects, framebuffer,
sound, and unlisted player/world fields are **not yet compared**. The reference
also emits `diagnostics.mapActorStates` with state IDs, countdowns, and flags;
these aid investigation but are explicitly outside the shared comparison schema.
A matching report is not a claim that the complete saved game states match.

## Reports and reproducibility

The output directory contains:

- `input.lmp`, `commands.txt`: the exact executed prefix and decoded commands.
- `reference.jsonl`, `lean.jsonl`: complete traces, including initialization.
- `report.json`: first divergence, command, exact values, first difference per
  subsystem, and first difference per field over the entire run.
- `provenance.json`: WAD/demo hashes, reference revision/archive/observer/build
  executable hashes, instrumentation script hash, Lean executable hash, trace
  hashes, profile, and boundary description.
- Build/runtime logs; no game files are uploaded.

Reference source is freshly extracted and instrumented on every run. The observer
adds snapshot calls and bookkeeping for map-object identity; gameplay routine
bodies are not replaced. Unknown patch anchors cause an error. The source stays
under `artifacts/tick-reference`, separate from the existing function-level oracle.

You can also compare saved trace files:

```sh
./scripts/compare-demo compare artifacts/demo-comparison/reference.jsonl \
  artifacts/demo-comparison/lean.jsonl --out artifacts/recomparison.json
```

Standalone comparison checks schema, command equality, and record continuity,
but cannot attest to the files' origin: its report says `provenance_verified:
false`. A managed `run` hashes the actual executed inputs and artifacts and sets
that field true. Neither value is a cryptographic signature or formal proof.

The normal `scripts/test` suite covers malformed demos/traces, one-bit changes,
initialization mismatches, missing actors, differing command streams, direct
signed turns, arbitrary movement values, and the shared firing path. The pinned
E1M1 runs are separate integration checks requiring local shareware assets.

```sh
./scripts/test-demo-comparison
```

This integration check runs the 141-tic movement, 170-tic combat, 145-tic
moving-combat, 521-tic enemy-encounter, 1,961-tic shotgun-secret and 2,445-tic
e1m1-exit scenarios,
repeats each engine in fresh processes to check deterministic traces, checks a
reference trace against itself, and injects a one-bit position change at tic 42
to verify the exact reported boundary. A real engine divergence is saved as a
finding; failure of the harness checks exits nonzero.

## Spawn-to-exit route and crushed corpse state

`e1m1-exit` runs 2,445 ordinary input commands from the normal E1M1 spawn to the
normal exit request. Its first 1,961 commands are exactly `shotgun-secret`.
The input SHA-256 is
`cd6c966592da1d23d35be0e54ec3ed92652aebee8e02d05131d02afdf4e42c52`.
Initialization and every declared field match both original-executable
comparisons and the broader Chocolate diagnostic trace through the final tic.
The six regression scenarios total 5,383 tics; these include shared prefixes,
not 5,383 distinct gameplay transitions.

The final imp dies at tic 2,165. At tic 2,243, the closing door crushes its corpse:
original `PIT_ChangeSector` enters `S_GIBS` (895), with an indefinite countdown
of -1, clears solidity and sets height/radius to zero. Lean previously changed
the collision body and render proxy but retained death state 461. The original
DOS trace independently detects that exact difference in the saved pre-fix Lean
trace. The sector adapter now also enters the generated original gib state in
the runtime corpse; signed health and actor identity remain unchanged.

By tic 2,445 all six enemies have nonpositive health, the player has 21 health,
and the exit switch is used. DOS schema v6 observes `exitRequested` directly:
the pinned `G_ExitLevel` instructions at code offset `0x20d40` clear `secretexit`
and store 6 (`ga_completed`) in `gameaction`. Both global addresses are checked
against LE relocations and bound again in running memory. Non-normal exits,
other game actions at the snapshot boundary, and exit requests before the final
requested tic fail capture. The broader trace also checks linedef 330 changes
from special 11 to zero on the activation tic.

Tests cover the runtime corpse's state/countdown, dimensions, solidity and
preserved health; malformed exit observations and bindings; and deliberate
corpse-state/exit-request mutations at their exact boundaries. Integration
checks repeat the original and candidate traces in fresh processes.

This is a matching **spawn-to-exit-request trace for the declared fields**, not
whole-game equivalence. It does not cover every path through E1M1, all three
secrets, video/audio output, `G_DoCompleted`, intermission or the E1M2 transition.

## Shotgun secret and damaging floors

`shotgun-secret` is a 1,961-tic continuous demo from E1M1's normal spawn. Its
first 521 commands are exactly `enemy-encounter`; it changes neither the WAD nor
the initial player state. The input SHA-256 is
`10c14af0dca28e097573c436f6f4edd509ad025cd235d9fef47ab537fb831f25`.
Initialization and all 1,961 post-tic snapshots match both candidate comparisons
against original DOS DOOM and the broader Chocolate diagnostic comparison.
The first five regression scenarios total 2,938 tics; that total includes the shared prefix,
not 2,938 distinct gameplay transitions. The integration checks repeat the DOS
run, require both profiles to match, and inject gameplay/miscellaneous RNG changes
at tics 1,249 and 1,886 to verify detection.

The route includes imp attacks and death, more zombieman combat, damaging slime,
the second door, the secret's lowering-floor trigger, medikit/shell/shotgun
pickups, secret counting, automatic weapon switching and three shotgun blasts.
The weapon is equipped with 28 shells by tic 1,881 and has 25 at tic 1,961.
These inventory and weapon observations now come directly from **DOS memory**
and also match the broader diagnostic trace, as do the imp fireball observations
described above. Other projectile types, the full death/rebirth lifecycle, level completion, audio
output and video output remain outside this route's claims.

The first new diagnostic mismatch was tic 1,249: the original lost five health
to sector-7 slime and consumed a pain RNG draw; Lean did neither.
`LevelSpecials.floorDamage` now ports ordinary damaging sectors 5, 7, 4 and 16.
It checks equality with the actual sector floor before XY/Z movement, uses
pre-increment level time, and runs before use, weapon actions and power counters.
The damage callback has null source/inflictor and uses normal armor, health,
pain and death handling without knockback. With a suit, sectors 4/16 still draw
RNG on every grounded visit, before checking the 32-tic damage interval. The
special-11 finale/god-mode/exit branch remains unported by this function.

`tests/test_floor_damage.py` extracts the unchanged pinned C
`P_PlayerInSpecialSector` body, observing damage requests and the original RNG.
43,008 cases agree at `-O0` and `-O2`, exhausting RNG seeds across all four
damage specials, suit states, raw floor-equality boundaries and clock edges.
Runtime tests also check armor, invulnerability, entering a floor on a damage
tic, and protection on the exact tic a suit expires. This is testing, not a
new correspondence theorem.

The second mismatch was tic 1,828: the collected medikit disappeared in the
reference, but scene resynchronization rebuilt an inert Lean actor with its
`removed` flag cleared. Disabled map slots now remain removed and unlinked;
the trace and actual collision scene use the same representation. A regression
checks removal persists through later ticks and that inactive skill entries
never appear as live actors.

## Initialization corrections

The first traces exposed an RNG index of 5 instead of 144, a prematurely computed
view position, and a pistol starting ready instead of rising. The corrected map
loader consumes `P_SpawnMobj`'s lastlook draw for every spawned object, then
`P_SpawnMapThing`'s duration draw only for positive initial state countdowns.
Players take the special spawning path; inactive skill/multiplayer entries and
unused player/deathmatch starts consume no draws. The metadata is generated from
the hash-pinned `info.c`; map order determines which object receives each value.
E1M1 on this profile consumes 92 lastlook draws, 51 duration draws and one lighting
initialization draw, reaching index 144 naturally. No index is patched to match.

The weapon now enters its up state and runs `A_Raise` immediately (initial Y=122),
while `viewz` stays zero until the first player tick. Logical sound setup and its
audibility-gated pitch draw now execute with or without PCM output, before later
status-face randomness. These fixes make the broader Chocolate trace match all
declared fields for the movement case as well, including the previously different
sector-40 lighting. This does not establish arbitrary movement/combat parity.

## Impact objects and firing order

After initialization was corrected, the firing sequence first diverged at tic 45:
the original advanced gameplay RNG from 144 to 149; Lean reached only 145. The
missing four draws belonged to `P_SpawnPuff`: two for signed height jitter, one
for `P_SpawnMobj`'s lastlook, and one for initial duration. Blood uses the same draw
order. Low-damage blood and melee puffs then change state and replace the duration,
while retaining all four draws. Each pellet creates its effect before applying
damage and before the next pellet draws randomness.

`Doom/Impact.lean` now owns those objects, their fixed-point Z movement, gravity,
floor/ceiling contacts, state countdowns and removal. New effects receive their
first thinker update in their creation tic. They do not enter BLOCKMAP collision
lists. The renderer uses their exact positions, original PUFF/BLUD states and
fullbright flags; expired objects leave the live array. Merely discarding four
random values would not reproduce this behavior.

`tests/impact_reference.py` runs unchanged original `P_SpawnMobj`, `P_SpawnPuff`,
`P_SpawnBlood`, `P_ZMovement`, `P_MobjThinker` and `P_SetMobjState` in a bounded C
host. The 1,752 sequences compare 48,168 snapshots at both compiler optimization
levels, covering every RNG starting index, damage thresholds, melee overrides,
wrapping jitter, spawn-height sentinels, contacts, countdowns and removal. The host
supplies a single sector and allocation/link stubs; this is not a world-collision
or general thinker-scheduler oracle. Unit/integration tests also cover misses,
nonblocking effects, seven-pellet ordering, reset, drawing and expiry.

These corrections eliminate the tic-45 RNG difference and its later lighting
consequences. General thinker interleaving, complete actor behavior and broader
demo coverage are still pending. Impact objects themselves are not yet included
in the original-executable trace schema; their state evidence comes from the
separate original-C oracle and the runtime regressions above.

## Player action / movement ordering

The moving-fire scenario first exposed a mismatch at tic 45: reference puff
`(x,y)=(74912276,-189005068)` versus Lean `(74828879,-189005703)` in raw fixed-point
units. Every previously captured field still matched. Comparing live effects
made the incorrect shot origin observable.

The live runtime now separates `P_PlayerThink`'s turn/thrust and view calculation
from the player's XY/Z mobj movement. Use and weapon actions run between those
phases, then player counters tick, then movement can collect items. Shots thus
use the updated angle and the pre-movement position. A newly collected key cannot
unlock a door used earlier in that tic; a newly collected shotgun cannot start
lowering the pistol until the next PlayerThink. Regression fixtures cover these
boundaries alongside the exact moving-fire trace.

This repairs one scheduling boundary. General thinker interleaving, remaining
enemy AI and full damage behavior still need ports. Effect positions are currently
checked against Chocolate, not directly against DOS memory.

## First enemy encounter and local correspondence proof

The encounter first diverged at tic 276: Lean created a door thinker but delayed
its first movement until the following tic. Door updates now run after player
actions and actor/light updates, including on the creation tic. This fixes that
boundary without claiming a complete port of the dynamic thinker list.

Zombiemen now share the ported imp state-machine core with their original state
table, alert variants, chase decisions, missile-range rules and attack cadence.
Their attack action performs original aiming, spread and damage draws in order.
An independent C action oracle compares 88,576 command snapshots at both `-O0`
and `-O2`. Its sight/collision hooks are fixtures and its `A_PosAttack` stub emits
an attack request; it does not independently verify the resulting hitscan/damage.
The full encounter exercises that integration separately.

The first version matched initialization and all declared fields through tic
380. Tic 381, the first damaging zombie bullet, exposed different player momentum
and both RNG indices. Player damage advanced the broader match through tic 425;
enemy knockback then differed at tic 426. The expanded DOS observer independently
detected that latter mismatch. The monster-motion correction below now matches
all 521 tics against both profiles. Both managed commands exit 0 for this case;
the integration requires a complete match rather than accepting a truncated run.
These remain finite, field-limited comparisons.

`Doom/ActorClock.lean` supplies the countdown decision used by live imp/zombieman
updates. `Doom/Proofs/ActorClock.lean` proves that decision equals an independent
operational transcription of the original decrement/check branch for **every
32-bit countdown**, including -1 and wraparound. A second theorem says that a
relation between two host states survives the update if their countdown setters
and state-entry continuations preserve it. Those are explicit hypotheses, not
proofs of the actions themselves. Both theorems are kernel checked and use only
`propext`, with no `sorry` or native decision axiom.

The original countdown bytes are pinned at code-object offsets `0x314d4` through
`0x314fa` in the DOS profile. Their connection to the operational model is manually
justified; this new theorem does **not** decode and verify x86 execution as the
arithmetic certificates do. XY/Z movement, nightmare respawning, state-entry
action correctness, and whole-enemy/whole-game correspondence remain outside it.

## Player damage and pain-state timing

`Doom/PlayerDamage.lean` ports the player's damage arithmetic and gates from
`P_DamageMobj`: shootable/alive checks, skull-flight momentum clearing, baby-skill
scaling, thrust before protection, the strict fall-forward condition and RNG
draw, sector-11 protection, the damage-1000 invulnerability bypass, armor,
signed overkill, damagecount clamping, lethal return and the surviving-hit pain
draw. Thrust preserves both wrapping intermediate products before signed
division. The live engine uses its existing normal single-player skill profile.
God/baby/chainsaw gates are tested core inputs, not new viewer features.

The runtime writes thrust into both the collision scene and player body so the
next movement tick consumes it. Inflictor coordinates are separate from credited
attacker identity: a projectile pushes from its impact location and a barrel
from its own location. Health, armor, counters and attacker bookkeeping follow;
lethal hits enter the existing kill path before any pain draw.

`PlayerAnim` tracks the live player's world-body states independently of weapon
psprites. A surviving pain response enters the four-tic `S_PLAY_PAIN`; the sound
runs on entry to `S_PLAY_PAIN2`. Movement, stopping, weapon-ready and firing update
that body state at their original phases. Starting an attack can replace a
pending pain animation, preventing its sound. The countdown runs after player
movement and before the enemies, so a later enemy hit starts counting next tic.

The independent host executes unchanged `P_DamageMobj`, `R_PointToAngle2`, fixed
arithmetic and RNG routines for 8,992 cases at both `-O0` and `-O2`, exhausting RNG
seeds and covering protection thresholds, armor exhaustion, lethal/fall-forward
boundaries, zero damage, source/inflictor gates and wrapped momentum/products.
Kill and state entry are explicit fixture stubs, not full gameplay. A second
output checks 16 animation steps per case against original state metadata;
runtime audio regressions check the four-tic delay and firing interruption.

This is **not full `P_DamageMobj` or DeathThink parity**. Player mobj targeting,
threshold/reaction flags and player corpse motion remain outside this port.
Enemy damage action/retargeting integration remains partial; its thrust and
momentum phases are now covered below. No new mathematical theorem is claimed
for this player-damage milestone.

## Monster knockback, corpse motion and expanded DOS observation

`DamageThrust.apply` is shared by the player and supported monsters/barrels.
It uses the original actor mass (400 for demons, 100 for the other supported
types), wrapping products, angle quantization and conditional fall-forward draw.
Thrust is applied before lethal damage, and its momentum survives entering death
states. Projectile and barrel inflictors retain their own coordinates even when
kill credit belongs to a different source.

`MonsterMotion` ports the nonplayer/nonfloating/nonmissile movement branches.
The existing asymmetric split rule retains a pending second attempt after a
blocked first attempt. Monsters stop at obstruction instead of sliding like
players. Friction preserves the airborne and corpse-on-ledge exceptions, with
the original strict thresholds. Conditional Z movement applies gravity and
floor/ceiling clipping. The live adapter uses real collision links and special
crossing callbacks, then runs the actor's live or death state countdown.
Coordinates remain exact fixed point in the scene; the map's integer projection
does not replace them after movement.

The independent C host runs unchanged `P_XYMovement`, `P_ZMovement` and the
original thrust branch with explicit move-acceptance hooks. Its 23,296 sequences
produce 41,472 snapshots at both optimization levels: all RNG seeds and lethal
fall-forward thresholds, mass/source gates, momentum clamping, positive split
remainders, blocked moves, stopping/friction thresholds, corpse ledges, gravity
and ceiling/floor contact. It is a movement-kernel oracle, not an independent
collision-map oracle. Runtime fixtures separately check immediate knockback,
continued corpse motion and wall blocking; the full E1M1 route checks composition.

The DOS observer adds X/Y/Z, momentum X/Y/Z, and signed health at validated mobj
offsets 12/16/20, 72/76/80 and 108. Each offset is checked against displacement
bytes in the original spawn or thinker instructions. The read-only observer
first caught zombie 87's missing momentum/position at tic 426 in the pre-fix
engine. After the fix, both candidates match its expanded fields for all 521
tics, and Lean also matches every broader diagnostic field, including subsequent
impact positions. The three earlier cases still pass, for 977 tics total.

This does not establish arbitrary-map or whole-game equivalence. Floating/skull
actors, the full death/rebirth lifecycle, complete damage actions/retargeting, exact dropped-item
spawn state/coordinates and general dynamic thinker ordering remain work. No new
formal proof is claimed for the momentum milestone.
