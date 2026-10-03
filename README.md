# (Lean)DOOM

A native Lean 4 reimplementation of the classic DOOM engine, targeting original
DOOM and DOOM II WADs. It now loads vanilla-format levels and renders first-person
views with WAD artwork, interactive doors, pickups, and a growing combat loop.
**The fist, pistol, shotgun, four enemy types, damage, and death/restart work. Full gameplay and level progression remain in development.**

The goal is a faithful port expressed idiomatically in Lean. The current playable
build is a prototype: its movement, combat, and rendering still contain
approximations and have not demonstrated vanilla demo or pixel compatibility.
Replacing those approximations now takes priority over expanding gameplay.

Map/artwork decoding, BSP traversal, rendering, and player movement are written in Lean.
A small C adapter provides SDL2 window, input, clock, and framebuffer presentation.
Python constructs independent test fixtures, drives executable tests, and serves the optional local proof view. There
are no Lean package dependencies and no embedded C DOOM engine.

## Play E1M1

Requires Lean 4.33.0 (via [elan](https://github.com/leanprover/elan#installation)),
Python 3, SDL2, and pkg-config. On macOS, install the latter tools with
`brew install python sdl2 pkg-config`; on Debian/Ubuntu use
`sudo apt install python3 libsdl2-dev pkg-config`.

```sh
git clone https://github.com/alaskahoffman/leandoom.git
cd leandoom
./scripts/fetch-shareware
./scripts/viewer
```

For the live movement and autoaim proof visualizations, run `./scripts/demo`
instead of `./scripts/viewer`. Place the wide proof window below the game.
WASD moves, arrows turn, Shift runs, Ctrl or left click fires, Space uses doors,
and 1/2/3 select fist/pistol/shotgun once acquired. Esc quits; R restarts.

The engine and audio synthesis run in Lean; SDL handles the platform boundary.
The formal proofs cover selected arithmetic and geometry properties, not the
whole engine. See [the proof companion](#live-proof-companion) and
[the roadmap](docs/ROADMAP.md) for the exact scope.

Source code is **GPL-2.0-or-later**; see [COPYING.md](COPYING.md) and the upstream
attributions in the source files. DOOM game data belongs to its respective rights
holders and is not included in this repository. The fetch script obtains and
verifies the original shareware distribution separately.

## Run

Install [elan](https://github.com/leanprover/elan#installation) if needed; the
`lean-toolchain` file pins Lean **4.33.0**, matching the current edition of
[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

```sh
./scripts/fetch-shareware
./scripts/lake build
./scripts/lake exe lean-doom inspect artifacts/doom-shareware-1.9/doom1.wad
./scripts/lake exe lean-doom validate artifacts/doom-shareware-1.9/doom1.wad
./scripts/lake exe lean-doom map E1M1 e1m1.svg artifacts/doom-shareware-1.9/doom1.wad
./scripts/lake exe lean-doom render-combat E1M1 '1:0' e1m1.ppm artifacts/doom-shareware-1.9/doom1.wad
```

The default development assets are id Software's original **DOOM shareware 1.9**,
containing Episode 1 (E1M1–E1M9). The fetch script downloads the original
[shareware archive](https://ftp.gwdg.de/pub/misc/ftp.idsoftware.com/idstuff/doom/doom19s.zip),
checks SHA-256 for both the archive and WAD, and extracts the WAD without running
DOS executables. It retains the original archive and readme locally. Expected
hashes and map identities are in `tests/reference/shareware.json`; files stay
under ignored `artifacts/doom-shareware-1.9/`. No game assets are included in the
source repository or covered by its source-code license. `--offline` verifies
an existing WAD or extracts a previously downloaded archive without networking.

Use `MAP01` with a separately supplied DOOM II WAD. Open the generated SVG in an image viewer or browser.
The diagnostic automap shows all geometry: red walls, blue special linedefs,
gray ordinary two-sided lines, green player starts, and gold other things.
Secrets and hidden lines are deliberately visible in this development tool.

PWADs go after the base archive, in load order:

```sh
./scripts/lake exe lean-doom map MAP01 map01.svg /path/to/doom2.wad /path/to/patch.wad
```

Later duplicate lump names and map markers win. A replacement map must contain
its complete map group in a single archive; incomplete replacements are errors.

On the development machine, `scripts/lake` also recognizes the official macOS
ARM64 compiler unpacked into `.tools/lean-4.33.0-darwin_aarch64`. That ignored,
local toolchain does not alter the system installation. Other machines can use elan.

## Interactive viewer

Install SDL2 and pkg-config (`brew install sdl2 pkg-config` on macOS, or the
SDL2 development package and pkg-config on Linux), then run:

```sh
./scripts/viewer
# Explicit map/WAD selection remains available:
./scripts/viewer E1M2 artifacts/doom-shareware-1.9/doom1.wad
```

With no arguments, the viewer verifies the local shareware WAD and starts E1M1.
Run `./scripts/fetch-shareware` once if it is not installed yet.

| Control | Action |
| --- | --- |
| W/S or up/down arrows | Forward/back |
| A/D | Strafe |
| Left/right arrows | Turn |
| Ctrl or left mouse button | Fire selected weapon (hold to repeat) |
| 1 / 2 / 3 | Select fist / pistol / owned shotgun |
| Space | Use a nearby door or switch |
| F | Toggle walking / free camera |
| Q/E | Fly down/up (free camera only) |
| Shift | Move faster |
| R | Reset the level, inventory, doors, and player |
| Escape or window close | Quit |

The viewer starts in walking mode, with wall/solid-thing collision, a 16-unit
player radius, 56-unit height, 24-unit step limit, headroom checks, and gravity.
Walking updates at 35 Hz independently of presentation. F enables free flight;
pressing F again returns to the last walking position. R resets to player start.
Walls, floors, ceilings, skies, transparent midtextures, and animated idle sprites
use WAD artwork. Space traces 64 units ahead to use a door or a door switch.
The window title shows interaction feedback, keys, health, armor, and ammo.
Combat uses the WAD-backed status bar: health, armor, ammo, weapon ownership, keys,
and the animated face. Original PLAYPAL damage/pickup/power feedback colors the screen.
Walk over keys and pickups to collect them; unusable health/ammo items remain.
Zombiemen, shotgun enemies, and demons can see you, pursue, attack, take damage,
and die. On death, press R to reset the whole level. Free flight pauses combat.
The framebuffer is 320×200 with a 90-degree horizontal field of view. Combat uses a
320×168 world view above the 320×32 status bar; inspection flight remains 320×200.

Headless rendering needs no SDL dependency. `render` uses player 1's start,
with the eye 41 units above the containing sector's floor. `render-at` takes
integer x/y/z world coordinates and an angle in degrees, where zero faces east:

```sh
./scripts/lake exe lean-doom render-at E1M1 frame.ppm -416 256 41 90 artifacts/doom-shareware-1.9/doom1.wad
```

`render` and `render-at` require valid artwork resources and report missing or
malformed assets. Use `render-flat` / `render-flat-at` with the same arguments
for the original diagnostic colors or geometry-only WADs.

Scripted walking is available without SDL or artwork resources:

```sh
./scripts/lake exe lean-doom walk E1M1 350 2 /path/to/doom.wad
```

This applies one key mask for up to 10,000 ticks and prints `position x y feet vz`.
Masks: forward 2, back 4, strafe left/right 8/16, turn left/right 32/64, fast 512;
add masks to combine keys. These are exploration controls, not vanilla ticcmds.

The interaction simulation also supports reproducible scripts:

```sh
# Walk for 27 ticks, press Space once, wait for the door:
./scripts/lake exe lean-doom simulate E1M1 '27:2,1:4096,70:0' state.json /path/to/base.wad
./scripts/lake exe lean-doom render-sim E1M1 '27:2,1:4096,70:0' frame.ppm /path/to/base.wad
```

Scripts are comma-separated `ticks:keymask` segments, capped at 10,000 ticks total.
Space is bit 4096. Holding it does not retrigger: release it for a tick before using
again. `simulate` exports a state summary without requiring artwork; `render-sim`
loads every required idle frame and switch texture and renders the resulting state.
The older `walk` command remains an isolated movement diagnostic. `render` and
`render-at` retain time-zero poses and need only spawn-frame artwork.

An optional three-room fixture lab retains Freedoom as a secondary test asset set;
normal development and previews now use the original shareware maps:

```sh
python3 tests/interaction_lab.py artifacts/interaction-lab.wad
./scripts/viewer E1M1 artifacts/freedoom-0.13.0/freedoom1.wad artifacts/interaction-lab.wad
```

Walk toward the door to collect the blue key and shotgun, then press Space. The
north wall has a tagged blue-key switch that opens the same door permanently.
The far room contains a zombieman and an animated torch. Open the door and use
Ctrl or left click to fight; the dropped clip is collectible. The PWAD contains only
original test geometry and things; it does not copy IWAD artwork.

Combat scripts use the same command format, with firing on bit 8192, restart
on bit 1024, and fist/pistol/shotgun selection on bits 16384/32768/65536:

```sh
./scripts/lake exe lean-doom combat E1M1 '27:2,1:4096,65:0,40:8192' fight.json \
  artifacts/freedoom-0.13.0/freedoom1.wad artifacts/interaction-lab.wad
./scripts/lake exe lean-doom render-combat E1M1 '27:2,1:4096,65:0,40:8192' fight.ppm \
  artifacts/freedoom-0.13.0/freedoom1.wad artifacts/interaction-lab.wad
```

The SDL viewer enables combat by default. `combat` and `render-combat` enable the
same actor/weapon update in the shared simulation; `simulate` and `render-sim`
retain passive actors for isolated interaction and idle-animation diagnostics.
Combat rendering validates all supported enemy poses, their dropped items, and
PISGA/B/C and PISFA weapon artwork. JSON summaries include shots, kills, enemy
positions/health/state, gameplay RNG index (`rng`), presentation RNG index
(`miscRng`), inventory, geometry, and weapon phase. They
are inspection snapshots, not complete savegames or cross-platform determinism proofs.

Individual assets can also be exported (transparent texels appear magenta):

```sh
./scripts/lake exe lean-doom asset texture SKY1 sky.ppm artifacts/doom-shareware-1.9/doom1.wad
./scripts/lake exe lean-doom asset flat FLOOR0_1 floor.ppm /path/to/doom.wad
# `asset patch <lump-name> ...` exports a raw patch.
```

PPM files can be viewed or converted by standard image tools; on macOS:

```sh
sips -s format png frame.ppm --out frame.png
```

The viewer build script supplies SDL's library path and recompiles the Lake
configuration to avoid stale local paths. Its generated entry point runs Lean's
viewer loop on the OS main thread, as required by macOS AppKit; normal CLI tools
retain Lean's default runner. The toolchain is pinned because this integration
depends on Lean 4.33's generated C entry point and IO ABI.

## Implemented

- Bounds-checked IWAD/PWAD directories and little-endian binary reads.
- Signed coordinates, case-insensitive lump lookup, zero-length markers, and
  ordered archive overrides.
- Vanilla `THINGS`, `LINEDEFS`, `SIDEDEFS`, `VERTEXES`, `SEGS`, `SSECTORS`,
  `NODES`, `SECTORS`, and `BLOCKMAP` decoding. `REJECT` bytes are retained.
- Geometry references, subsector ranges, BSP references/cycles, and blockmap
  lists checked before automap rendering.
- Command-line inspection, validation of every map, and SVG automap export.
- Signed 16.16 camera storage, wrapping 32-bit angles, and tested arithmetic
  primitives. `Fixed.divChecked` implements reference saturation and signed
  truncation, including zero-divisor saturation. It explicitly rejects raw
  `INT_MIN` operands whose `abs` behavior is undefined in the C reference.
  The older `Fixed.div?` remains a separate diagnostic helper.
- Exact sine, tangent, and arctangent tables from the pinned source, with lengths
  encoded as Lean vectors and proof-checked lookup bounds. `SlopeDiv` retains
  unsigned wrapping; point-to-angle conversion retains the original octant/axis
  asymmetries. These foundations are tested independently; the current viewer's
  movement/projection still use the earlier floating-point implementation.
- BSP sector queries and bounded front-to-back traversal. Side classification now
  follows the reference's wrapping differences, sign shortcut, and rounded
  fixed-point products, including near-partition ties.
- Near-plane/screen clipping, one-sided walls, upper/lower portal spans,
  floor/ceiling regions, and per-column occlusion, rendered in Lean.
- RGB24/PPM output and an optional SDL2 walking/free-camera viewer.
- `PLAYPAL` palettes and `COLORMAP` index remapping, including original damage,
  pickup, berserk and radiation-suit palette selection in combat. Fixed player
  colormaps and high-detail invisibility fuzz are connected as described below.
- `PNAMES`, `TEXTURE1`/`TEXTURE2`, column/post patches, clipped patch composition,
  transparency, and 64×64 flats. Required patches are cached while composing a map's
  textures; all map artwork is loaded once before the viewer loop.
- Perspective-correct wall coordinates, sidedef offsets, upper/lower/one-sided
  pegging, world-coordinate floor/ceiling mapping, and masked midtexture composition.
- Episode/map sky selection and suppression of upper walls between sky sectors.
- Spawn/idle appearance for 115 vanilla thing editor numbers, including directional
  rotations, paired mirrored frames, sprite offsets, ceiling attachment, and fullbright
  frames. Single-player medium-difficulty flags select map things. Player starts,
  teleport/spawner markers, and unknown thing types are not drawn.
- Per-pixel depth tests for sprites, opaque surfaces, and transparent midtextures.
- Reference-tested player acceleration, friction, BLOCKMAP collision, three-corner
  wall sliding, gravity, step recovery, and view bobbing. The free camera remains available.
- Shared 35 Hz simulation for the SDL viewer and scripted CLI: manual doors,
  keyed doors, tagged door switches, repeatable buttons, and moving ceiling collision.
  Normal doors move 2 units/tick, fast doors 8, and raised doors wait 150 ticks.
  Movement and door thinker kernels now use original fixed-point arithmetic,
  strict destination tests, countdowns, obstruction responses and removal rules.
  Closing raise-doors reopen when blocked by the player or a solid map actor;
  close-only doors wait at the obstruction instead of crushing it.
- Original map-spawned sector light effects: broken-light flashes, fast/slow
  strobes (including synchronized ones), glow and fire flicker. The original
  countdowns, gameplay RNG calls and signed-short light writes are reference-tested.
  Walkover triggers turn tagged lights on/off or start strobes, preserving one-shot
  clearing, repeat behavior, callback order and the shared-brightness quirk.
- Blue/red/yellow cards and skulls, health and armor, ammo, backpack capacity,
  weapon ownership/ammo grants, and power-up inventory/timers. Collected items
  disappear; closed walls prevent collecting items through them.
- Idle/spawn frame sequences with individual tick durations and fullbright flags.
  Decorations and unsupported monsters animate in place. The initial combat roster
  has explicit chase, attack, pain, and death states.
- Pistol windup, first-shot accuracy, repeated-shot spread, ammo use, WAD weapon
  overlays, muzzle flash, and original fixed-point hitscan and portal-clipped vertical autoaim.
- Zombieman (3004), shotgun enemy (9), and demon (3002) combat. Sight and bullets
  check wall intersections and vertical portal clearance. Pursuit respects walls,
  monster-blocking lines, steps, actors, and the player. Enemy bullets are blocked
  by shootable actors, including barrels; killed enemies lose solidity at their original `A_Fall` state action.
- Green/blue armor absorption, invulnerability protection, player death and full
  restart. Zombiemen drop five-bullet clips; shotgun enemies drop a shotgun with
  four shells. Existing pickup caps and ownership rules apply.
- Separate gameplay and presentation random streams with byte indices, reset,
  and ordered subtraction. Their lookup bounds and stream independence are proved
  in Lean; full table sequences are checked against the pinned C reference.
  Combat uses the gameplay stream, but its call order and AI decisions still do
  not match vanilla demos.

Resource lumps use last-definition-wins archive lookup. Within the selected
TEXTURE1 followed by TEXTURE2, the first matching texture definition wins, as in
vanilla. Patch sprite offsets are decoded separately and do not alter texture
placement origins. Nonempty patch/texture dimensions are limited to 2048×2048;
extended tall-patch conventions and modern texture formats are unsupported.

Projection uses floating point. Actual WAD colors/light tables are used, but
light-table selection and sky projection are approximate. Texture wrapping uses
the image dimensions rather than emulating vanilla's non-power-of-two quirks.
Texture/flat animations and most actor AI/action callbacks remain unimplemented. Frames are
repeatable on the tested platform, but are not bit-exact vanilla output or
guaranteed identical across platforms. The renderer trusts structurally validated
map references; it does not prove that an arbitrary map's BSP describes valid
convex subsectors.

Sprite frame names resolve within each archive's S_START/S_END or SS_START/SS_END
namespace, with standalone unnamespaced PWAD replacements also supported. This
avoids collisions with unrelated names such as BOSSBACK. Each matching later view
overrides earlier views. Missing
required rotations and malformed sprite patches are errors. The actor catalog
contains spawn/idle appearance, timing, and dimensions, with no DeHackEd or custom
actor support. Animated modes validate all required frames before running; missing
frames or paired switch textures produce an error. Idle cycles currently start in
sync instead of reproducing vanilla's randomized initial state delays.

Walking now uses the reference-tested fixed-point player movement sequence:
keyboard tic commands, acceleration, original split moves, BLOCKMAP collision,
wall sliding, friction, view bobbing, and gravity/step recovery. It honors the
WAD's BLOCKMAP, including omissions, and propagates unsupported-domain errors
instead of falling back to approximate movement. Door movement/thinker kernels
are reference-tested; use dispatch, obstruction detection, combat and actor
spawning/updating still include prototype behavior. No demo or full-tick parity
is claimed. Original walkover lighting handlers are wired into crossing callbacks;
E1M1’s fast lowering floor (36) and repeatable lift (88) also use original
spawn/movement rules. Other floor/lift kinds and crushers remain future work.
The F toggle never places a walking player at an unchecked free-camera location.

Supported **use-activated door specials**:

| Family | Linedef numbers |
| --- | --- |
| Manual raise/open; normal, locked, fast | 1, 26–28, 31–34, 117–118 |
| Tagged raise/open/close switches and buttons | 29, 42, 50, 61, 63, 103, 111–116 |
| Tagged locked fast-open switches/buttons | 99, 133–137 |

Door switches change their SW1/SW2 texture; repeatable buttons restore it after
35 ticks. Switch actions target matching nonzero sector tags. Unsupported use
specials report their number. Other walkover actions and floor/lift kinds,
crushers, exit transitions, and timed sector specials are still pending. Normal
exit switch 11 now flips its texture and queues completion; gameplay holds there
until the original intermission and next-map stages are implemented.

The fist, pistol and shotgun are usable. Keys 1/2/3 select them; picking up the
shotgun equips it through the original lowering/raising sequence. Other weapon
pickups retain ownership and ammo for later implementation. Zombiemen, shotgunners, demons
and imps attack. Imps use original sight/chase/attack states, scratch at close range,
and throw moving, dodgable fireballs. Barrels take damage, explode and chain-react.
Other unsupported monsters remain idle props. Death sequences for the remaining
monster types and level transitions are still pending. E1M1 music and sound effects
now play in the viewer; see the audio profile below.

Combat is not yet vanilla equivalent. Imp look/chase/face/attack routines now use
the original normal-speed single-player rules, including eight-direction movement,
sector hearing, ambush checks and selected monster-operated door behavior. Other
enemy AI and the global player/thinker scheduling still use prototype adapters. Shooting uses the
original fixed-point traversal. Supported death sequences use the original state
tables, including delayed loss of corpse solidity and extreme deaths. Full damage
thrust, general infighting and global thinker/RNG ordering remain pending.
The WAD-backed status bar replaces the development text, crosshair and RGB tints.
It uses a 320×168 view, original digit/icon positions, and an animated face.
Weapon offsets and frame metadata come from the WAD/original state tables;
the supported weapons now use original switching, bobbing and attack states.
Active ammo follows the weapon readied at the bottom of the lowering sequence. Original HUD messages,
menus, intermissions and configurable view sizes remain separate work. See the
status-bar scope in `docs/ROADMAP.md`.
Invulnerability protection and inverse colormaps, and light-amplification colormaps
work. Other power-up effects beyond inventory/timers/healing,
including invisibility, radiation protection, and an in-game automap, remain pending.

The `validate` command checks map structure; artwork is checked during textured
rendering/export. These checks do not establish whether a level is playable.
They do not interpret REJECT, enforce all vanilla
engine limits, or emulate vanilla handling of malformed maps. Hexen/UDMF maps
and extended/compressed nodes are outside this milestone.

## Weapon selection and shotgun

Press **3** after collecting a shotgun, **2** for the pistol or **1** for the fist.
A new shotgun pickup requests an automatic switch. Switching waits for the current
attack to finish, lowers the old weapon at six pixels per tic, changes the ready
weapon/ammo display at the bottom, then raises the new weapon. Holding a selection
key does not repeatedly lower an already readied weapon. Restart restores the pistol.

`Doom/Weapon.lean` replaces the pistol animation timer with the original supported
`P_SetPsprite`/`P_MovePsprites` countdowns and ready/lower/raise/refire actions.
`WeaponData.lean` is generated from pinned `info.c`. It preserves weapon-before-
flash ticking: a newly started flash loses its first tic in that same update.
The shotgun fires after three windup tics, spends one shell, traces seven pellets
with one shared autoaim slope, and repeats every 37 tics while held. Every pellet
performs its own damage/spread draws and applies damage before the next pellet;
pain/death randomness is therefore interleaved. Shotgun frames, its two flash
frames, `DSSHOTGN` sound, weapon bobbing and status-bar shell counts are connected.
The fist handles the no-ammo fallback, including 64-unit reach, berserk damage,
impact sound and facing the struck target.

```sh
./scripts/test-weapon-reference
```

The separate `tests/reference/weapons.json` pins unchanged C routines, source and
harness hashes, and **68,480 commands** agreeing at both `-O0` and `-O2`. The corpus
checks weapon/flash states, positions, refire/latch, ammo, light levels, sound and
pellet requests, and RNG with supplied damage callbacks. Ten runtime/reference
regressions cover ownership, pickup switching, mid-pump changes, seven pellets,
empty-ammo fallback, fist range, sprites/audio, restart and script partitioning.
Real E1M1 checks relocate only the player start to its actual shotgun pickup,
equip it, fire seven pellets for one shell, and switch back to the pistol.

This verifies these weapon routines and their integration, not complete combat
or demo parity. The map-start adapter still begins with the pistol ready instead
of running `P_SetupPsprites`; full player mobj attack-state/thinker ordering,
blood/puff spawning and its RNG, original damage/thrust, and other weapons remain
pending. Muzzle flash patches are fullbright; the ported extra-light state is
recorded, but its world-lighting effect still awaits the renderer lighting port.
Unsupported weapon pickups retain their pending request without equipping them.

## E1M1 sound and music

The viewer now plays the WAD's digital sound effects and looping `D_E1M1` score.
DMX sample decoding, MUS sequencing, GENMIDI instruments, the nine-voice music
driver, FM synthesis, spatialization and mixing all run in Lean. SDL only queues
signed 16-bit stereo PCM: exactly 1,260 frames per 35-Hz game tic at 44,100 Hz.
Restart resets both music and effects. Music and effects default to volume 64/127.

```sh
./scripts/viewer
# Explicit silent mode for unsupported/custom music or a machine without audio:
./scripts/viewer --no-audio E1M1 artifacts/doom-shareware-1.9/doom1.wad
# Five seconds of the same music/mixer and scripted gameplay, including pistol fire:
./scripts/lake exe lean-doom render-audio E1M1 '35:0,35:8192,105:0' artifacts/e1m1-sound-demo.wav artifacts/doom-shareware-1.9/doom1.wad
./scripts/test-audio-reference
./scripts/test-shareware
```

Effects include pistol/shotgun fire, punch impacts, pickups, doors, switches, lifts, blocked use, hard
landings, player/monster pain and deaths, imp attacks/fireballs and barrel blasts.
They use eight channels with the original distance/stereo rules, priorities,
same-origin replacement and sound-pitch `M_Random` calls. Moving sources follow
their actual positions; removal stops their sound. Pitch never consumes gameplay
`P_Random`. Audio-enabled runs share the miscellaneous stream with the status face;
ordinary headless simulation diagnostics leave playback disabled. Replay JSON
includes `audioEvents`; `render-audio` also writes a WAV-sidecar state/trace report.

The selected music profile is DOOM 1.9's nine-voice OPL2 driver with immediate
register writes, using a Lean port of Alexey Khokholov's GPL Nuked OPL3 1.8 melodic
OPL2 synthesis path. Integer envelopes, operator pipeline, feedback, vibrato,
tremolo and resampling follow the pinned implementation. Independent original-C
fixtures at both `-O0` and `-O2` verify MUS conversion, driver writes, 2,912 spatial
cases, 2,576 channel commands and 168,128 stereo FM frames. Sources, hashes and
expected outputs are pinned separately in `tests/reference/audio.json`.
The real shareware E1M1 check matches all **5,828 MUS events**, the complete music
register trace and the first **220,500 stereo PCM frames** against C. Its score
loops after 13,440 MUS ticks (96 seconds). Twenty runtime/parser/reference tests
cover audio, in addition to SDL queue/lifecycle checks.

These are software-profile comparisons, not DOS hardware recordings or full-demo
parity. MUS uses an exact 140-Hz loop clock without Chocolate Doom's extra 5-ms
restart guard; hardware register-write latency and analog output are not modeled.
Digital effects use linear interpolation and the reference's measured DMX pitch
approximation, rather than claiming original DAC waveform equivalence. OPL3,
hardware rhythm mode, external MIDI, General MIDI playback, PC-speaker effects,
linked chaingun sounds, episode-four music remapping and volume controls remain
outside this milestone. E1M1 percussion uses GENMIDI melodic voices and is covered.
Full sound-event interleaving depends on the remaining thinker/AI ports: non-imp
alert choice/cadence and player damage timing still use the prototype adapters
(zombiemen/shotgunners currently use `posit1` for alerts). The independently checked
channel and synthesis routines do not establish those remaining gameplay timings.

## Live proof companion

Run `./scripts/demo` to open E1M1 with sound and a separate browser window of
minimal mathematical diagrams on black. Momentum vectors and an autoaim side
profile share the screen with their inequalities; expand “Lean source” for the
compilable examples using those exact observed integers.
The proof view is a wide horizontal strip: place its window below DOOM for recording,
and keep keyboard focus on the game.
The browser updates at 10 Hz from read-only snapshots produced by the Lean viewer.
Use `./scripts/demo --no-audio` for silent recording, or pass a map and WAD as
with `scripts/viewer`. `--no-browser` prints the local URL without opening it.
The launcher uses an available localhost port and cleans up when the viewer exits.

The movement diagram uses momentum captured immediately before/after the engine's
friction call, after collision handling. Lean proves that each component's absolute
value, and consequently squared horizontal speed, cannot increase in this function.
This holds for every signed 32-bit velocity, including negative rounding, ground
friction, airborne preservation, stop-speed snapping and no-momentum mode. It is
not a theorem of an entire movement tic, collisions or strafe-running speed.

The autoaim diagram records the actual last pistol/shotgun shot: selected probe,
portal openings, target height, clipped slope interval, chosen slope, distance and
actual pellet yaw angles. The shaded region is the clipped vertical interval;
the yellow line is the aiming ray. A small top-down yaw inset distinguishes
side-probe autoaim from the actual fired direction. Side probes choose only pitch;
they do not redirect horizontal aim, and shotgun spread still applies.

`autoaim_center_inside` proves that DOOM's signed midpoint stays in every nonempty
clipped interval within the original ±40960 raw slope bounds, with division toward
zero even for negative odd sums. `autoaim_trajectory_inside` proves that its relative
vertical rise remains between the boundary rays for **every** distance from 0 to
1024 map units, using actual `Fixed.mul` rounding without overflow. These are
arithmetic guarantees on the supplied window, not proofs of BSP/BLOCKMAP traversal,
correct target selection, absolute-height addition, or a guaranteed hit. The
production autoaim calls the same midpoint function used in the proof. The diagram
uses scaled axes and continuous lines; numeric examples use exact fixed-point
integers. No-target or out-of-domain observations do not claim a proved instance.

Ammo/pellet and state-table timing proofs remain in `Doom/Proofs/Firing.lean`,
although the display now focuses on geometry. The reference-test corpus continues
to check original autoaim ordering, historical misses and weapon behavior.

These are **theorems checked at build time, with live observed instances**. The
browser is not running a new proof search every frame. It explicitly marks missing,
stale or disconnected telemetry and clears shot observations when the game resets.
Exact squared values are strings over JSON to avoid JavaScript integer rounding;
speed readouts alone are rounded. Each displayed source file contains valid Lean examples,
and regression tests compile actual movement and pistol/shotgun snapshots. `scripts/demo.py` only launches processes and
serves the local page and snapshot; movement, combat and sampling stay in Lean.

Proof sources: `Doom/Proofs/Movement.lean`, `Doom/Proofs/AutoAim.lean`, `Doom/Proofs/Firing.lean`.
Run `./scripts/lake env lean ProofAudit.lean` after building to inspect dependencies:
only Lean's standard `propext`, `Classical.choice`, `Quot.sound` axioms (or none),
with no `sorryAx`, custom axioms or native-evaluation trust extension.
The viewer imports these proofs, so an invalid theorem prevents its build.

## Tests

A C compiler and the pinned upstream reference sources are needed for the full
suite. Fetch the small, hash-checked reference files once (no game assets):

```sh
./scripts/fetch-reference
./scripts/test
# Optional SDL boundary/lifecycle tests, using SDL's dummy video driver:
./scripts/test-viewer
```

The committed reference corpus is losslessly gzip-compressed in
`tests/reference/expected.json.gz`; tests read it directly using Python’s standard
library. No Git LFS or external corpus download is required.

Tests generate a small original room WAD in temporary storage. They exercise
signed geometry through the SVG output, overrides within/across archives, every
truncated prefix of a fixture, malformed directory fields, bad map references,
BSP cycles/shared children, blockmap errors, and command-line failures.
The two-room fixture checks projected portal boundaries against independently
calculated screen coordinates, closed-door occlusion, back-side views, near-plane
clipping, and reproducible frames. Artwork tests independently encode patches and
texture tables, check every truncated patch prefix, palette index 255, clipping,
transparent posts, overrides, UV coordinates, pegging, plane projection, sky
portals, and light-table application. The slanted-wall fixture checks UVs against
an independent ray/line intersection, including a clipped endpoint.
Sprite tests cover all eight rotations, mirrored origins, transparent pixels,
lighting, archive overrides, ceiling attachment, walls, portal lintels, and grates.
Walking tests cover radius clearance, slanted walls, fast-movement tunneling,
sliding, headroom, the exact step limit, gravity, solid things, and repeatability.
Interaction tests cover use distance/side/occlusion, held-button debouncing, all
key colors, manual reversal, tagged switches, button reset timing, door clearance
and obstruction, pickup caps/removal, idle timing/fullbright changes, namespace
collisions, rendered switch changes, and scripted repeatability.
Combat tests cover pistol timing/ammo/spread replay, nearest hits, wall/portal
occlusion, facing/hearing/ambush, pursuit and monster-blocking lines, melee and
hitscan attacks, armor/invulnerability, pain/death sprites, dropped items,
nonblocking corpses, player death/restart, weapon offsets, and missing assets.
Current result: **365 Python test groups plus 80 Lean checks pass**. Eighty-two groups
compare **788,115 cases** against checked-in outputs from independent C routines:
wrapping addition/subtraction, fixed multiplication, BSP side classification,
map-node conversion, interleaved RNG streams/reset, supported fixed division,
all 16,385 trig table entries, every fine-angle bin boundary, unsigned slope
division, point-to-angle conversion, keyboard tic commands, thrust at every fine
angle, player command ordering, unobstructed horizontal movement/friction,
vertical movement, view-height recovery/bobbing, combined physics traces,
collision point/box predicates, ordered player position checks, move acceptance,
sector/block relinking, immediate crossed-special callback ordering, path
intersections/traversal, fixed slide projection, three-corner wall sliding,
connected player movement, the runtime WAD/keyboard adapter, pickup grants,
touch eligibility/effects, stateful pickup sequences, ordered movement contact,
pickup editor metadata extracted from the original mobj/state tables, live
player counters, power expiry, renderer colormap precedence, and high-detail fuzz
columns with shared phase and mutable indexed-framebuffer reads. Later additions
cover status widgets, lighting, use tracing, scrolling, plane/door movement,
sector clipping, E1M1 floor/lift spawning and thinker steps, secret sectors,
normal exit-switch activation, the original switch lists, fixed-point
hitscan/autoaim over the original BLOCKMAP traversal, and original kill/death-state
actions for the supported combat roster.
Seven pixel-test groups additionally check actual WAD table lookup on surfaces,
masked walls, fullbright/transparent sprites, sky and opaque weapon/flash patches,
including first-tic delay, blink/expiry, missing rows and archive overrides.
Current smoke checks pass on all nine DOOM 1.9 shareware maps with combat
rendering at tick 35, plus an eight-frame SDL dummy-driver viewer run. Earlier
Freedoom 0.13.0 validation covered 68 maps, 35 forward-input tics and 20 coasting
tics (26 items collected across those routes). These smoke checks are not vanilla
parity comparisons.
The C routine bodies and renderer selection blocks
come from hash-checked Chocolate Doom 3.1.1 sources at commit
`410d96855b5df5410ff591a90efeafa889119224`; they agree at `-O0` and `-O2`
under the recorded 32-bit wrapping/arithmetic-shift profile. Normal tests run
offline. These are function/selection-block comparisons, not full-engine or DOS demo tests.

To reproduce the C comparisons (requires a C11 compiler):

```sh
# Downloads missing pinned reference files into ignored artifacts/:
./scripts/test-fidelity --fetch
# With reference sources already cached, uses no network:
./scripts/test-fidelity
```

The manifest and golden outputs live in `tests/reference/`. Source hashes and
corpus hashes are checked; mismatches report the first input and differing result.
Regenerate golden outputs only deliberately with `--record`, then review them.
Fixed division's `INT_MIN` inputs are excluded from C comparisons: upstream uses
`abs(INT_MIN)`, which has undefined C behavior. A separate test checks Lean's
explicit rejection of those inputs; it is not evidence of DOS parity. No host
result for this undefined case is treated as a DOS specification. The C profile
also records the compiler-dependent signed shifts used by these routines.

The tables are generated by extracting integer literals, without reevaluating
trigonometric functions. With sources cached, check the generated module with
`python3 scripts/generate-tables.py`; `--write` regenerates it deliberately.

`Doom/Ticcmd.lean` implements signed command fields and keyboard movement/fire/use:
sixth-tic turn acceleration, run/strafe speeds, opposing-key cancellation, and
the 50-unit sideways-command clamp. `Doom/Motion.lean` implements player thrust
and horizontal momentum with fixed arithmetic, preserving diagonal speed,
positive-only movement splitting, truncation versus shift rounding, strict stop
thresholds, and airborne friction behavior. Its step-count bound is proved in
Lean; behavioral agreement is tested against C, not formally proved.

`Doom/PlayerPhysics.lean` adds player gravity, floor/ceiling contact, step-up view
recovery, hard-landing squat and sound events, and view bobbing. It retains the
initial double gravity impulse, the strict hard-landing threshold, floor-before-
ceiling clipping, and the airborne view-clamp overwrite. Bobbing uses the original
integer phase increment and a bounds-checked table index. Landing sound events
are recorded and played by the audio-enabled runtime.

The physics test environment accepts every `P_TryMove` attempt and checks
each attempted position, momentum, angle, and standing/running-state transition.
Combined traces chain keyboard building, `P_MovePlayer`, `P_CalcHeight`, horizontal
movement, and conditional vertical movement. View calculation precedes body motion,
as in the reference player/thinker ordering. They compare drops, ceiling contacts,
landings, view recovery, and changes to the fixture floor height. These omit map
collision/slide handling, reaction-time delays, sector/weapon actions, animation
ticks, and other thinkers. Keyboard coverage excludes mouse/joystick, weapon/special
commands, and demo turn quantization/serialization. Separate connected fixtures
now exercise real collision/sliding; the viewer uses that movement sequence.

The diagnostic executable `.lake/build/bin/motion-probe input.txt` reads one
fixture command per line. For example, `reset` followed by repeated `tick 129 1`
applies running-forward input; `tick 0 1` releases it and allows friction to act.
Output fields before `|` are forward, side, turn, buttons, and turn-held count;
after it are raw x/y, momentum x/y, unsigned angle, frame ordinal (0 standing,
1–4 running), attempt count, and each attempted x/y pair. Fixture key bits are
1 forward, 2 backward, 4 left, 8 right, 16/32 strafe left/right, 64 strafe modifier,
128 run, 256 attack, and 512 use. They are separate from the viewer's input mask.

For combined vertical/view behavior, `physics 129 1 0` runs the isolated movement
sequence at leveltime 0; increment the final argument each tic. `space FLOOR CEILING`
changes the fixture's floor/ceiling in raw 16.16 units. For example, after `reset`,
`space -4194304 8388608` lowers the floor 64 units and starts a drop on subsequent
physics steps. An additional `|` separates the vertical/view output: body z,
vertical momentum, floor, ceiling, body height, no-gravity flag, view height,
view-height delta, view z, bob magnitude, and landing sound-event count.

`Doom/Collision.lean` now ports player position checks with solid/inert actors:
thing cells before line cells, x-major/y-minor traversal, supplied actor-list order,
square thing contact, early blocking, duplicate-linedef suppression, and ordered
floor/ceiling/dropoff/special-line results. It retains the BLOCKMAP leading-zero
quirk: linedef 0 is visited even when a cell's payload is empty. The line-side
predicate is separate from the BSP predicate, matching the original arithmetic.
Tests compare both the result and exact thing/linedef visitation order against C.

`Doom/Move.lean` adds `P_TryMove` acceptance and commit: space/height checks,
the exact 24-unit step and dropoff boundaries, teleport/no-clip exceptions, and
the intermediate `floatok` result. Successful moves update x/y and floor/ceiling
without immediately raising z. Sector and BLOCKMAP lists preserve order; moving
within the same cell still reinserts the actor at the head. Failed moves retain
pickup effects and item unlinking while leaving the moving actor in place.

Crossed-special callbacks run immediately after relinking, in reverse contact
order, with the original old-side argument. Later contacts re-read the actor's
position and line special flag. Tests use recording, line-disabling, and actor-
repositioning callbacks to check this behavior. These are test effects, not ports
of DOOM's special actions. Callbacks that perform nested position queries and
overwrite vanilla's global contact scratch are outside the verified domain.
Pickup effects and actual special-action handlers remain pending.
The collision/move/slide routines now drive walking and have their own connected
physics traces alongside the unobstructed tests. More than eight contacted
specials, unsupported signed-short BLOCKMAP data, and unverified abs(INT_MIN)
cases return errors. They are not silently approximated or labeled compatible.

`Doom/Path.lean` ports ordered line/thing interception and `P_PathTraverse`:
the one-unit block-boundary nudge, line-before-thing cell visits, distinct divline
rounding, and first-inserted equal-fraction order. It keeps the 64-iteration limit
even when rounding stalls in one cell. Lines are deduplicated; things are not.
Fixtures compare every cell visit, collected intercept, and visitor invocation,
including early exits and a stalled trace producing exactly 128 intercepts.
More than 128 intercepts are rejected explicitly; historical buffer-overrun
behavior remains unverified. Traversal visitors are read-only.

`Doom/Slide.lean` ports the original three-corner sliding sequence: fixed corner
order and hit ties, the `0x800` approach margin, quantized angle projection,
two retries, and Y-then-X stairstepping. It preserves the distinction between
the two-sided flag and a back sector, and between slide interception and the
subsequent move acceptance check. C comparisons cover attempted moves, momentum,
actor links, path traces, and recording-only special crossings.

`Doom/WorldPhysics.lean` connects command thrust/turn, view calculation, horizontal
movement/collision/sliding/friction, and conditional vertical movement in the
reference order. A failed half-move slides using full current momentum, then
still attempts the saved second half. The connected C fixture uses the actual
unchanged collision and slide functions and compares every attempted move,
final momentum/height/view, actor links, and special crossings over sustained
traces. These comparisons do not include full thinker or special-action behavior.

`Doom/Player.lean` adapts this core to the viewer and CLI: it preserves keyboard
turn-held state, keeps fixed body/view state between tics, and uses BSP sectors and
the WAD's BLOCKMAP. Actor lists persist across tics; changed prototype actors are
relinked, and changed sector heights refresh the collision geometry. Runtime
fixture tests compare WAD-driven walking, strafing, running, turning, sliding and
coasting against pinned C results. The old floating-point walking code is removed;
free flight remains an independent renderer-inspection control. Scripted JSON
now includes momentum, binary angle, view height, and landing-event count.

`Doom/Pickup.lean` ports the single-player, unmodified DOOM 1.9 `P_GiveAmmo`,
`P_GiveWeapon`, `P_GiveBody`, `P_GiveArmor`, `P_GiveCard`, `P_GivePower`, and
`P_TouchSpecialThing` effects. It includes all 36 pickup sprites, difficulty-based
ammo amounts, dropped weapons, pending-weapon selection, six separate card/skull
slots, backpack capacities, powers/shadow state, player and mobj health, item
counts, bonus counters, message identifiers, removal decisions and sound events.
Height limits are inclusive, and subtraction wraps before comparison. Tests retain
the medikit's post-healing message check, duplicate-key bonus behavior, and the
megasphere's commercial-mode restriction. Original functions, ammo constants,
weapon/ammo associations and default health/armor limits come from pinned sources.

The collision core now invokes these effects in original thing-list order,
before line/height rejection. Consumed items unlink immediately, preserving the
iterator's successor; failed moves retain inventory, removal, message and sound
events. Solid pickup actors retain the original cached solidity for the current
check. No-clip bypasses contacts, and a player with zero XY momentum performs no
movement pickup query. Contact uses strict square bounds, not radial distance or
a separate line-of-sight test: pickups can be consumed through a blocking wall.
Door-driven height queries also perform contacts, including for an idle player.

The viewer/CLI now use this path. `Inventory` bridges the remaining prototype
combat/UI fields; its old grant logic and the independent proximity scan are
removed. Map removal is reflected before drawing, dropped ammo retains its flag,
and keys/skulls and pending weapons persist. JSON exposes `cards`, `pendingWeapon`,
`pickupBonus` and `itemCount`. The runtime currently uses medium skill, with
commercial mode selected for MAP-prefixed maps. Original English messages and
pickup editor numbers/dimensions/count flags are pinned from `d_englsh.h` and
`info.c`. The new C fixtures exercise contact, unlinking, move rejection and
connected movement; all 308,467 earlier reference cases are unchanged.

`Doom/PlayerCounters.lean` now ports the live counter stage of `P_PlayerThink`:
berserk counts upward, timed powers/damage/bonus counters decrement when nonzero,
and invisibility clears `MF_SHADOW` only when its decrement reaches zero.
Invulnerability takes priority over light amplification even on its dark blink;
colormap selection uses the original post-decrement 128-tic threshold and bit 3.
Signed wrapping and negative counter behavior remain explicit.

The runtime calls this stage before movement contacts. New pickups retain their
full duration on the collection tic; a newly collected visual power is selected
on the next tic. Inventory conversion preserves berserk age and shadow state.
Dead players skip live counter updates, and inspection flight pauses them. JSON
adds `strengthTics`, `shadow` and `fixedColormap`. The independent C oracle compiles
the entire unchanged `P_PlayerThink` with inert movement/view/weapon dependencies
and a stubbed `P_DeathThink`: these fixtures verify counters and the early dead
return, not those dependencies or the complete player tic. All 324,315 previous
reference results are unchanged.

`Doom/RenderLighting.lean` connects fixed colormaps to the textured view.
Walls (including masked midtextures), floors, ceilings, ordinary world sprites
and opaque weapon/muzzle-flash patches use the selected WAD row instead of normal
sector/distance lighting. Fixed rows override fullbright sprites; sky always uses
row zero, retaining the original invulnerability exception. RGB values come from
COLORMAP lookup followed by PLAYPAL; no approximate RGB inversion is used. The
normal light selector remains clamped to 0..31, while inverse row 32 is accessed
as an actual effect row. A 32-row WAD still supports normal/infrared rendering;
trying to draw an inverse frame without row 32 reports an explicit error. Patch
WAD overrides supply the same tables used by the main view. Inspection flight
keeps its independent unaffected camera. Status artwork bypasses COLORMAP but
shares the screen-wide PLAYPAL palette, as in the original.

The independent oracle extracts unchanged selection blocks from R_SetupFrame,
R_MapPlane, R_DrawPlanes, R_RenderMaskedSegRange, R_ProjectSprite and R_DrawPSprite.
It supplies normal light rows and checks fixed/fullbright/sky/fuzz precedence at
both optimization levels. All 361,801 earlier comparisons remain unchanged.
`Doom/Fuzz.lean` now ports the original high-detail `R_DrawFuzzColumn`.
It uses the original 50-entry offset table, skips the top/bottom view borders,
samples the indexed framebuffer one row above/below, applies COLORMAP row 6,
and observes earlier writes within the same post. Fuzz takes precedence over
inverse/fullbright maps. Spectres (editor 58) and invisible weapon/flash posts
use this path, preserving transparent holes and clipping against world depth.
Rendering now retains palette indices alongside RGB: duplicate RGB palette colors
cannot destroy the source index. Background sprites draw before nearer fuzz
sprites, with deterministic map-order ties in the current renderer.

The SDL renderer owns fuzz phase across posts, sprites and presentations, even
without a simulation tic and across game restarts. Single-frame CLI exports start
at phase zero; they do not pretend to reproduce an unrendered frame history.
Unchanged C `R_DrawFuzzColumn` and its original table independently check every
phase, viewport border, empty span, repeated draw and full-buffer checksum.
All 366,793 earlier comparison results remain unchanged. Adapter tests cover
post holes, duplicate palette colors, inverse/invisibility precedence, blink
transitions, occlusion, sprite order and repeated presentation phase.

This verifies the high-detail column drawer at a 320-pixel stride, viewport origin
zero and view heights 3..200. Low-detail drawing, other viewport origins, original
sprite projection/post rounding, BSP visitation/tie ordering, normal distance/weapon
lighting and full pixel parity remain separate work.

Multiplayer persistence, DeHackEd, the remaining weapons, general thinker
deletion and item respawn remain pending. Status palette selection is ported;
the prototype combat bridge now supplies damage counters/attacker identity, but
full P_DamageMobj and DeathThink are not ported. Pickup sounds are recorded and played in the viewer. The surrounding combat loop remains a prototype;
full-tick/demo parity is not established. Supported death routines are covered below.

`Doom/SectorLights.lean` ports the original map-spawned lighting thinkers for
sector specials 1, 2, 3, 4, 8, 12, 13 and 17. It finds minimum adjacent light
through two-sided lines, spawns in sector order, clears consumed specials, and
preserves special 4's damage marker. Its damage effect itself is still pending.
The port retains bitmask random delays, synchronized initial counts, strobe dark/
bright periods, glow's endpoint step reversal, and fire's current-light comparison
and minimum-plus-16 behavior—even when that minimum exceeds the starting maximum.
Each sector write narrows to the original signed 16-bit field.

Lighting runs once per simulation tic after the current actor updates, shares
`P_Random` with gameplay, and never advances on framebuffer presentation. It also
runs in passive simulations and during inspection flight, when combat is paused.
Restart rebuilds thinkers and RNG from the original map. JSON snapshots now
include `sectorLights`, `sectorSpecials` and `lightThinkers`; rendering reads the
updated sector levels through the existing COLORMAP selector.

The independent oracle compiles unchanged spawn/tick/neighbor routines and the
original sector-dispatch block, with non-lighting special handlers stubbed out.
It checks 34,708 new cases at -O0/-O2, preserving all 392,133 previous results.
Fixtures cover every initial RNG byte, mixed thinkers, interleaved gameplay RNG,
short narrowing, disconnected/self-referencing/one-sided topology, and external
light changes. WAD tests cover timing, original quirks, random-stream separation,
restart and actual rendered light changes. `.lake/build/bin/lights-probe input.txt`
runs these rule fixtures. Generalized thinker insertion/removal, original
actor-spawn RNG, and exact actor/door interleaving are still pending.
This establishes lighting routine parity, not whole-map RNG,
full-tic, demo, or framebuffer parity; normal distance lighting remains approximate.

Walkover lighting linedefs 12/13/17/35/104/79/80/81 now execute immediately inside
the movement callback, in original reverse contact order. Both crossing directions
work; these actions accept players only. Failed movement and merely touching a
line do not activate them. One-shot specials clear even when no tagged sector
matches or every strobe target is busy; repeatable specials remain active. The
numeric map special and collision flag update before the next movement callback.

The port preserves tag-zero matching, sequential sector writes, and
`EV_LightTurnOn`'s shared-brightness quirk: once a neighbor search finds a nonzero
level, subsequent tagged sectors reuse it. Starting a strobe checks `specialdata`,
appends without replacing existing light thinkers, clears the sector special, and
consumes gameplay RNG in sector order. The runtime currently supplies busy sectors
from prototype doors; other movers are pending. New strobes tick later in the same
simulation tic. Light use-switch actions and nested position-query specials are
still pending.

An additional 47,872 comparisons run unchanged `EV_*` routines, tag search,
the original nonplayer gate and eight crossing case blocks at both optimization
levels. All 426,841 prior cases are unchanged. WAD integration tests exercise real
crossings in both directions, simultaneous triggers, blocked moves, repeated
activation after an existing glow changes the light, duplicate thinkers,
same-tic countdowns, restart, script partitioning and rendered colormaps.

`Doom/Plane.lean` ports `T_MovePlane` for floors and ceilings in both directions.
It uses wrapping 16.16 arithmetic and strict overshoot comparisons. Landing
exactly on the destination returns `ok`; a later attempted overshoot returns
`pastdest`. An obstructed destination attempt restores the old height and calls
the sector-change callback again, yet still returns `pastdest`. Ordinary upward
ceiling movement ignores an obstruction reply. Crushing floors/ceilings and
non-crushing rollback retain their original branch differences. Callback state
survives rollback, so actor effects can be supplied when `P_ChangeSector` is ported.

`Doom/VerticalDoor.lean` ports all eight `T_VerticalDoor` types, including signed
countdown decrement, waits, reversal, removal, and sound requests. The runtime's
existing normal/fast raise, open and close actions now use these kernels. For a
normal door moving from -16 to 124 at speed 2, the 70th movement tic reaches 124;
the 71st starts the 150-tic wait. Fast doors preserve the original extra closing
sound on removal, and obstruction reversal requests the ordinary opening sound.
JSON `doorSounds` records that tic's thinker sound requests; the viewer plays them.

The oracle adds 57,930 cases from unchanged C bodies, comparing raw heights,
callback/rollback order, state, removal and sound events at `-O0` and `-O2`.
All 474,713 previous cases are unchanged. WAD tests compare six existing door
actions to frozen C states at movement/wait/removal boundaries, alongside blocked
closure, reversal, restart and script partitioning. `.lake/build/bin/doors-probe`
runs these fixtures. Runtime actor selection and non-crushing disposition now use
the sector-change port described below; crush damage and blood remain pending.
Door activation/target selection, general thinker order and deferred removal also
remain pending. Delayed and close-then-open types are kernel-tested but not yet
spawned by runtime map actions. Runtime door targets/speeds remain whole units;
the independent kernels test fractional raw fixed-point values too.

`Doom/HeightClip.lean` ports `P_ThingHeightClip` and connects it to the real,
effectful position query. Floor followers use exact old `z == floorz` equality;
airborne actors move only when forced down by a ceiling. The routine ignores the
query's boolean success and uses its resulting floor/ceiling limits, including
early returns before line traversal. It preserves signed 32-bit arithmetic.
Non-player queries honor monster-blocking lines; this can prevent a query from
seeing a low adjacent ceiling. No-clip still bypasses contacts.

Runtime tentative door moves and rollbacks now run these queries, carrying actor
heights and pickup effects forward. An idle player may collect an item during a
door update; rollback does not undo collection or necessarily restore airborne Z.
Unsupported collision inputs propagate a physics error. The non-crushing
sector-change port now supplies the surrounding candidate scan and disposal policy;
crush damage, blood spawning and full actor lifetime management remain pending.

The oracle adds 5,728 cases using unchanged `P_ThingHeightClip`, both with supplied
limits and real `P_CheckPosition`/pickup routines. It covers fixed-point extremes,
floor following, forced airborne lowering, rollback sequences, doorway edges,
monster-blocking lines, rejected queries and retained pickup effects. All 532,643
earlier comparisons are unchanged. WAD tests cover idle collection, repeated
blocked closure, monster-line early returns, script partitioning and restart.

`Doom/SectorChange.lean` ports the non-crushing `P_ChangeSector` path. Sector
bounds include front/back linedef vertices, expand by the original 32-unit
`MAXRADIUS`, wrap fixed-point arithmetic and clamp each bound on only one side.
The scan follows block cells in x-major/y-minor order and live actor links within
each cell. A height query can collect a future item and remove it from that scan;
removing the current dropped item retains the original successor behavior.

When an actor no longer fits, dead bodies request `S_GIBS`, lose solidity and get
zero radius/height. Dropped objects are unlinked and removed. Other shootable
actors obstruct the move; solid decorations without `MF_SHOOTABLE` do not.
The original health-before-dropped precedence is preserved. Map-placed corpse
artwork has positive spawn health and is not mistaken for a killed enemy.
`Doom/ActorFlags.lean` supplies original spawn health and shootable/sector/block
flags for all 118 map actor types, generated by `scripts/generate-actorflags.py`.

Runtime doors use this scan on tentative moves and rollback. Gib sprites are
preloaded and drawn as `POL5A`; removed ammo awards no inventory or pickup event.
JSON exposes `gibbed` and `crushedDrops` as map-thing indices. Five WAD tests cover
expanded-block contacts, shootable versus solid policy, map corpses, combat death
and dropped ammo, restart/partitioning, and reopening with visible gib artwork.
Two Lean checks verify bounds assembly from map lines, including a back sector
without the two-sided flag. The oracle adds 3,687 comparisons against unchanged
C bounds/sector routines and original metadata expressions; all 538,371 previous
comparisons remain unchanged. Gib-state requests and unlinking are observed in
the C fixture, with thinker deletion/respawn/audio outside its scope. The API is
explicitly non-crushing: `crunch=true` damage/blood, complete actor state lifetimes,
original door activation and thinker timing still need ports. Runtime damage still uses the prototype adapter; supported death actions now use
the original kill routine and state chains described below.

`Doom/Use.lean` replaces the floating-point use ray with original `P_UseLines`
and `PTR_UseTraverse` behavior. The 64-unit endpoint uses the fine-angle tables
and wrapping integer products. BLOCKMAP lists determine which lines participate;
tied intercepts retain original order. Ordinary lines pass a use press if their
opening is positive, regardless of player height or blocking/two-sided flags.
The first special always stops traversal, and its original point-side result is
passed to the action adapter. A closed ordinary line requests the no-way response;
the viewer plays it. Door/switch action dispatch and its player-tick ordering
still use the existing adapters. This establishes use tracing; the normal exit action is described below, while
full door activation parity remains pending.

`Doom/Scrolling.lean` implements special 48 from the original list-initialization
and line-update blocks. It retains at most 64 linedefs in map order, rechecks their
current specials, increments front-sidedef offsets by one fixed-point unit per
tic, and preserves shared-sidedef multiple writes and signed overflow. Runtime
scrolling runs after the map thinkers and feeds the renderer's texture coordinates.
Other `P_UpdateSpecials` work, notably flat/texture animations and original button
timing, remains separate. JSON exposes `scrollers` and `sideOffsets`.

The C oracle adds 9,001 use-trace and 350 scrolling comparisons. All 542,058
previous comparisons remain unchanged. Use cases cover all fine-angle bins,
range endpoints, back sides, ordering, narrow/inverted/wrapped openings and
BLOCKMAP omissions. Scroll cases cover fractional raw offsets, overflow, list
mutation, shared sides and the 64-line boundary. WAD regressions also check the
actual rendered scroll and its interaction with use tracing. The earlier use
fixture's 64-unit eastward boundary was an approximation: the fine cosine places
the endpoint just short of that boundary. A wall omitted from BLOCKMAP also no
longer blocks the use ray; the blocking-wall fixture now explicitly includes it.

Development now prioritizes the features in shareware **E1M1**. Its exact specials
and remaining work are tracked in `docs/ROADMAP.md`. `scripts/test-shareware` runs
`tests/integration_e1m1.py` to verify the pinned map inventory and all eight live
scrolling linedefs at 0/1/35 tics, across script partitioning and restart. It also
checks actual floor/lift crossings with only the player start relocated in E1M1:
line 308 lowers sector 59 from 96 to −40; line 195 lowers sector 70 from 104 to
−48 and returns it to 104. These are focused geometry checks, not an end-to-end
run from the normal start. The same integration checks all three secret sectors
and the real exit switch, plus killing an imp and exploding a barrel through the
pistol path, and imp fireball spawning/geometry impacts. Intermission/E1M2 transition, nukage damage and
shotgun firing remain outstanding for the single-player milestone.

`Doom/FloorMover.lean` ports the special-36 `turboLower` floor and special-88
`downWaitUpStay` platform. Both move four units per tic. The floor uses the highest
neighboring floor plus eight, unless that height already equals its own floor;
the original −500 search sentinel and wrapping arithmetic are preserved. The lift
lowers to its lowest neighbor, waits 105 tics, returns, and removes its thinker.
Strict endpoint tests retain the extra completion tic. A blocked ascent reverses
without crushing damage; clipping/disposal effects survive plane rollback.

Spawning preserves sector order, tag-zero matching, busy-sector rejection,
one-shot consumption even when nothing spawns, repeatable lift triggers, and
original nonplayer/projectile gates. Exceeding the original 30 active-platform
limit reports an error. Player crossings spawn movers immediately, and new movers
can run on the activation tic. Runtime floor movement uses the same actual actor
height/clipping queries as doors, so players and pickups follow the floor.
Movement/start/stop sounds are exposed in JSON and played in the viewer.

`MoversProbe.lean` adds 43,432 comparisons against pinned C floor/platform routines
and selected unchanged spawn/crossing branches, agreeing at both optimization
levels. All 551,409 previous comparisons remain unchanged. Seven WAD regressions
cover activation/completion timing, riding, repeat triggers, busy sectors,
blocked-ascent reversal, reset and script partitioning. Monster crossing dispatch,
manual door use on an active platform, and complete interleaving with all original
thinkers remain unported; these checks do not establish full-tick/demo parity.

`Doom/Hitscan.lean` replaces the floating-point shooting cylinders with original
`P_AimLineAttack`, `P_LineAttack`, their callbacks, and `P_BulletSlope`. Both the
player pistol and existing hitscan enemies use live BLOCKMAP actor links and
clipped actor heights. Aiming and shooting retain actor-diagonal intersections,
line-before-thing cell visits, first-inserted ties, the one-unit boundary nudge,
and the path traversal's 64-cell limit. An omitted line is not recovered by an
all-lines scan. Non-shootable decorations and corpses do not absorb bullets.

Portals narrow the vertical aim interval. The first shootable actor's visible
height determines the slope, with signed midpoint rounding. Player autoaim tries
center, then +1/64 turn, then −1/64 turn at 1024 units; these choose vertical slope
without steering the fired horizontal angle. Shots travel 2048 units and use
strict height tests, original four-/ten-unit impact offsets and sky-wall rules.
Special-line requests precede wall tests; puff/blood requests precede damage,
including impact requests from zero-damage traces. Runtime JSON exposes the last
`shotSlope` and this tic's ordered `shotEvents`; source/target −1 means the player,
and other IDs are map-thing indices.

The C oracle adds 24,063 comparisons across all fine-angle bins, portal limits,
solid/shootable distinctions, tied targets, raw fractional ranges, sky cases,
impact positions, zero damage and BLOCKMAP omissions. All 607,341 prior results
remain unchanged. Eight runtime regressions cover the same live shooting path,
including a target-order case where the old cylinders chose the wrong enemy.
The enlarged combat test arena now supplies a BLOCKMAP covering its actual bounds.
Focused real-E1M1 checks hit zombieman 87 and barrel 35 from relocated starts.

A centered pistol shot can occasionally miss the zombieman near E1M1's zigzag
walkway because of the original BLOCKMAP corner-traversal stall. The reproduced
case visits the same grid cell until the 64-step limit, never reaching the target;
a one-map-unit step in any direction restores the hit. Unchanged C at `-O0` and
`-O2` matches Lean in the regression in `tests/test_hitscan.py`. This historical
behavior is preserved rather than widening hitboxes or altering traversal.

This ports hit selection and ordered requests, not all combat actions. Blood/puff
actor spawning, its RNG use and rendering, original damage/thrust/pain,
global weapon/thinker scheduling, remaining enemy sight/AI and shadow aim
perturbation remain pending. Supported weapon states/switching are covered above. The existing damage adapter handles the three supported enemies and the
player, imps and barrels; unsupported monsters still stop shots without damage actions.
Shoot-activated specials 24/46/47 report an explicit error when applicable; E1M1
contains none. Mutating shoot-special callbacks must be integrated before wider
map compatibility. Combat work now takes priority over the intermission handoff.

`Doom/Death.lean` now ports `P_KillMobj`, death-state entry actions and the finite
`P_MobjThinker` state countdown. `DeathData.lean` is generated from pinned `info.c`
for the player, zombieman, shotgunner and demon. Signed overkill health is retained;
extreme death requires health strictly below negative spawn health and a defined
extreme state. First-state duration consumes `P_Random()&3` and clamps to one tic.
Screams run on their original state entries, including their random sound choices.
Final states keep tics −1. Sound requests are recorded and played in the viewer.

Deaths keep their actor identity and linked-list position. They clear shootability,
set corpse/dropoff flags, and quarter the collision height. Monster solidity lasts
until `A_Fall`; player death clears solidity immediately. Original kill/frag credit
and player-dead state are retained. Clips/shotguns spawn immediately, retain dropped
pickup semantics, and consume the original item-spawn `lastlook` RNG draw. No map
corpse decoration is substituted for a killed actor. Replay JSON exposes signed
`death`/`playerDeath` state, flags, height, countdown, pose, frags and `deathEvents`.

The independent C oracle adds **17,728 comparisons** using unchanged `P_KillMobj`,
`P_SetMobjState`, scream/fall actions, original selected tables, and the unchanged
countdown block at `-O0` and `-O2`. All **631,404 previous comparisons** remain
unchanged. Ten runtime regressions cover thresholds, frames, timing, corpse
collision, shooting through dead actors, drops, player death, reset and script
partitioning. A real E1M1 check kills zombieman 87 through the pistol path and
checks its final corpse and drop using a relocated start.

The kill oracle observes weapon/automap/drop requests; it does not implement those
callees. Runtime item creation is still an adapter. Full `P_SpawnMobj`, corpse
momentum/gravity/friction, nightmare respawn, `P_DeathThink`, actual `P_DropWeapon`
psprite lowering and general thinker ordering remain unported. The supported
roster's kill and death-state behavior is covered, not complete combat or full-map
RNG parity. `P_DamageMobj`, blood/puff effects and original weapon states are next.

Imps (3001) and barrels (2035) now join the damage roster. Imp health/pain and
normal/extreme death frames come from the original metadata; live imp behavior
and projectiles are described below. Barrels retain their stationary idle state after
nonlethal damage, do not count as monster kills, and use original fullbright BEXP
frames. `A_Explode` runs on entry to BEXP4, after three five-tic states (with the
original first-frame random shortening). The barrel remains solid until S_NULL
unlinks it after the last explosion frame. Nearby barrels enter their own delayed
death chains. Radius victims include the player and supported combat actors.

`Doom/Radius.lean` retains original y-major BLOCKMAP/bnext order, shootable/boss
gates, Chebyshev distance minus victim radius, whole-unit falloff and the wrapped
`(damage+MAXRADIUS)<<FRACBITS` search bounds. `Doom/Sight.lean` supplies original
BSP/REJECT blast occlusion, three-way side tests (including the historical
horizontal equality typo), portal slope clipping and victim-to-barrel direction.
The sight target is the already-quarter-height barrel. Actors do not block sight.
A barrel remembers the first surviving hit's source; lethal damage returns before
retargeting, so blast credit does not automatically follow the killing shot.

Five new C groups add **75,105 comparisons**, including full imp/barrel death
sequences, original sight helpers/portal traversal, and radius gates, falloff,
block bounds and traversal. All **649,132 previous results** remain unchanged.
Ten runtime tests check damage/pain, blast delay/removal, chains, portal/REJECT
blocking, source attribution, reset and required sprite assets. Real E1M1 checks
shoot and kill imp 8 and explode/remove barrel 35 from relocated starts.

Blast requests feed the existing damage adapter; full P_DamageMobj thrust,
infighting and original general thinker ordering remain pending. Ordered request
collection is valid for this adapter's delayed barrel chains and stationary damage
callbacks; relocating/reentrant damage callbacks require further integration.
Blast sounds now play through the shared sound channels. This does not establish full combat/demo
parity. Restart an already-running viewer with `./scripts/viewer` to load changes.

`Doom/Imp.lean` now ports the original normal-speed single-player imp actions:
look, eight-direction chase, target facing, melee/missile selection and attack.
`Doom/ImpData.lean` is generated from pinned `info.c`, including live/pain and
fireball flight/explosion states. State-entry actions execute immediately, with
original countdowns, random draws, reaction/threshold counters, shadow aim and
same-species projectile immunity. The initial eastward movement direction is
preserved even when a newly awakened imp faces west.

`Doom/ImpRuntime.lean` connects those actions to BSP/REJECT sight, live fixed-point
BLOCKMAP movement, monster blocking/dropoff rules, persistent sector sound targets,
and manual door gates. `Doom/Projectile.lean` and `Doom/ProjectileRuntime.lean`
provide imp fireball spawning, half-step checks, flight, thing/wall/floor/ceiling
impacts, sky removal and explosion states. Fireballs are drawn at their actual
height using original fullbright BAL1 frames; they take time to reach a target and
can be dodged. Damage and death use the existing combat bridge.

Five new independent C groups add **63,878 cases**, bringing the total to
**788,115 across 82 groups** at both `-O0` and `-O2`. All **724,237 previous
results** are unchanged. Eleven runtime regressions cover startup/chase, facing,
hearing/ambush, closed portals, melee timing, projectile travel/dodging, wall
explosion/removal, monster door gates, reset and fullbright sprite rendering.
Real E1M1 checks also exercise imp fireballs against the original map geometry.

This verifies selected imp routines and their runtime integration, not full demo
parity. Fast/nightmare and multiplayer branches remain pending. Other actor spawn
RNG, full `P_DamageMobj` thrust/infighting and global thinker interleaving
are not yet original. Audio playback is implemented under the profile below. Projectiles retain creation order within their own
update pass after actors; manual doors still share the existing allocation adapter.
An already-running viewer must be restarted with `./scripts/viewer`.

`Doom/LevelSpecials.lean` implements secret-sector discovery and normal exit switch
11. The initial secret total counts sectors marked 9. A live player discovers one
only when body Z exactly equals that sector's floor; touching a higher neighbor
or hovering above it does not count. The signed counter increments and the sector
special clears, so revisiting cannot count it again. The runtime checks before
player XY/Z motion, retaining the original one-tic delay after entering/landing.
Restart restores both undiscovered sectors and counters. No extra secret sound or
HUD notification is added: those were absent in the original behavior.

Exit switch 11 accepts front-side player use, clears the special, selects the
first matching entry in the original switch list (then top/middle/bottom within
that entry), flips its texture and requests normal completion. Clearing happens
before sound selection, preserving the original `swtchn` rather than `swtchx`
quirk. An unrecognized texture still requests completion, without a switch sound.
The switch list uses the base archive's normal shareware/registered/commercial
map markers; a PWAD cannot change that mode. Other switch/door actions still use
the existing adapters. The historical button sound-origin pointer and playback
remain outside this port.

The exit activation tic finishes normally. The engine then holds the last level
state at the pending completion boundary, with an explicit viewer message;
`G_DoCompleted`, the original intermission and E1M2 loading remain unimplemented.
This is an exit request, not a completed level transition. JSON exposes `secrets`,
`totalSecrets`, `exitRequested`, `secretExit` and `exitSwitchSound`.

`LevelProbe.lean` adds 12,500 independent C comparisons for secret equality,
repeat visits, signed counter wrap, initial totals, switch lists, texture priority,
front/nonplayer gates and normal-exit requests. All 594,841 earlier cases remain
unchanged. Nine runtime tests also cover landing/entry timing, repeat discovery,
partitioning/restart, use reach/back sides, switch-mode selection and the pending
completion boundary. Focused checks in the real E1M1 discover sectors 68/69/70 and
use line 330 to change `SW1STRTN` to `SW2STRTN`, relocating only the player start.
Full PlayerThink/use ordering, sector damage and general thinker scheduling are
still pending; these checks are not end-to-end or demo parity.

The single-player status bar loads `STBAR`, `STARMS`, the tall/short digits,
percent signs, six key icons, ownership numbers and all 42 face patches from the
WAD. It honors patch offsets, transparent posts and archive overrides, with raw
palette indices rather than sector lighting. Number widths, negative clamping,
the 1994 no-ammo sentinel, skull-over-card precedence, and ammo row order follow
`st_lib.c`/`st_stuff.c`. All widgets redraw from their backing bar each frame;
original incremental dirty-widget behavior on unusually overlapping custom
patches is not claimed. `STTMINUS` is optional as in Chocolate Doom. A present
`STBAR` requires the remaining UI patches and all 14 PLAYPAL palettes. Minimal
render fixtures with no `STBAR` retain a 320×200 diagnostic view with no UI.

`Doom/Status.lean` ports face priorities/timers and palette selection. The face
updates after gameplay once per 35 Hz combat tic, consumes one `M_Random` byte
without touching `P_Random`, and is unchanged by extra presentations. The original
health-minus-oldhealth ouch bug, angle wraparound behavior, pickup grin, held-fire
delay (using the weapon-ready attack latch), god/dead faces and persistent function-static timers across `ST_Start`
are retained. Runtime attacker bearing uses the existing fixed-point angle core;
actor movement/damage production, the weapon-ready schedule, and the surrounding
ticker remain prototypes.
Original palette selection covers damage, bonus, berserk and suit blink, applied
once to the complete indexed world/weapon/bar buffer. Custom RGB tints are gone.

The C oracle checks 22,516 new number, palette, state-sequence and widget cases,
with all 369,617 earlier comparisons unchanged. WAD pixel tests cover digit and
patch placement, all key masks, armor/weapon pickups, the held weapon's ammo,
face timing/death/invulnerability, palette effects, resource errors, and fuzz
clipping at the status border. `.lake/build/bin/status-probe input.txt` runs the
rule fixtures. Multiplayer/frags, DOOM 1.0 split bars, view-size controls, original
HU messages, menus, intermission/finale screens and whole-frame parity are pending.

`.lake/build/bin/pickup-probe input.txt` runs the pickup fixtures in
`tests/pickup_reference.py`. `touch SPRITE ITEM_Z PLAYER_Z HEIGHT DROPPED COUNTED`
uses the adapter sprite order in `Doom/Pickup.lean` and raw 16.16 coordinates.
Touch output includes removal, sound, pickup inventory fields, and message ID.
`counters DAMAGE FIXED` and `think DEAD` exercise the separate counter stage;
think output includes all six powers, shadow, bonus, damage, fixed colormap and
dependency-call trace. These commands also support long grant/expiry sequences.
`light KIND FIXED NORMAL FULLBRIGHT SHADOW INVISIBILITY` exercises colormap
selection (kinds 0..5: wall, plane, sky, sprite, weapon, masked wall; output -1
means fuzz). It does not execute a full original rasterizer.
`.lake/build/bin/fuzz-probe input.txt` accepts `reset SEED PHASE VARIANT`,
`draw X LOW HIGH HEIGHT` (inclusive bounds) and `snapshot`; its C oracle is
`tests/fuzz_reference.py`, with column bytes and whole-buffer checksums.

For a static wall check using an actual WAD, with x/y/radius in raw 16.16 units:

```sh
.lake/build/bin/collision-probe --map-lines /path/to/doom.wad E1M1 0 0 1048576
```

This diagnostic loads geometry, uses BSP to find the destination sector, and
leaves actors out explicitly. Its output is `clear floor ceiling dropoff ceilingLine
specialCount specialIds... | thingCount thingIds... | lineCount lineIds...`.
`clear` means this position-check stage found no blocker; it does not certify a
legal complete move. The normal `collision-probe input.txt` interface accepts the
bounded scene commands in `tests/collision_reference.py` for actor-order fixtures.
Move fixtures add `world` (two sector heights and an x partition), `body` (actor
z/height/floor/ceiling/flags), `place` (initial linking), and `try ACTOR X Y`.
The latter reports acceptance, `floatok`, position-query results, all actor
positions/heights and sector/block list orders, then crossed-special events.
Fixture flag bits are 1 no-clip, 2 teleport, 4 dropoff, 8 float, 16 no-sector,
and 32 no-blockmap; they are adapters to the original C flag values.

`tests/path_reference.py` adds `path X Y ENDX ENDY FLAGS STOP_INDEX`
(flags 1 lines, 2 things, 4 early-out; stop index -1 continues),
`momentum ACTOR MX MY`, and `slide ACTOR`. Path output includes the adjusted
trace, cell iterator calls, collected intercepts, and visited intercepts.
Slide output includes final scene/momentum, each move attempt, all corner paths,
and crossing events. Coordinates and momentum use raw 16.16 integers.

SDL lifecycle checks also pass. After the BSP/RNG changes, all 68 Freedoom combat
smoke-test frames retain their previous hashes; this is a regression result,
not a vanilla framebuffer comparison.

Primary integration testing uses the verified original shareware WAD:

```sh
./scripts/test-shareware
SDL_VIDEODRIVER=dummy ./scripts/viewer --frames 8 E1M1 artifacts/doom-shareware-1.9/doom1.wad
```

**9/9 original Episode 1 maps validate and render after 35 combat ticks**, including
WAD-backed status artwork; the eight-frame SDL smoke test also passes. The report
is saved to `artifacts/doom-shareware-1.9/combat-smoke.json`. This validates asset
compatibility, not demo playback, original game progression, or pixel parity.

The existing 68-map Freedoom corpus remains optional compatibility coverage.
Obtain those WADs from the official
[Freedoom 0.13.0 release](https://github.com/freedoom/freedoom/releases/tag/v0.13.0):

```sh
./scripts/lake exe lean-doom validate /path/to/freedoom1.wad
./scripts/lake exe lean-doom validate /path/to/freedoom2.wad
python3 tests/integration_wads.py --combat /path/to/freedoom1.wad /path/to/freedoom2.wad
```

Integration result: **36/36 Phase 1 maps and 32/32 Phase 2 maps validate and render
nonempty textured frames after 35 combat ticks**. This is a smoke test, not a visual correctness
comparison against vanilla. The combat viewer completed a 180-frame native macOS presentation run in
2.21 seconds; SDL boundary/lifecycle checks pass with the dummy driver.
Original commercial DOOM WADs have not yet been tested. No WAD assets are tracked
in this repository; the development copies and automap are under ignored
`artifacts/`.

## Engine direction

The target is real DOOM behavior and data compatibility. Rendering, simulation,
resource decoding, and gameplay belong in Lean. The platform adapter provides
a window, events, a clock and PCM device output through Lean's C ABI.

Lean types, explicit state, functional decomposition, and proofs should make the
engine easier to reason about. Internal structures can differ from C while
preserving observable behavior: arithmetic and rounding, 35 Hz timing, update
and random-call order, collision rules, and historical quirks. A proof must state
the property and assumptions it establishes; bounds safety alone does not prove
DOOM compatibility.

The immediate priority is to pin a behavioral reference, build comparison tests,
and replace the prototype's arithmetic and simulation foundations. See
[the implementation roadmap](docs/ROADMAP.md) for the fidelity policy and next steps.

## Code map

| File | Responsibility |
| --- | --- |
| `Doom/Binary.lean` | Checked byte reads and fixed-size records |
| `Doom/Wad.lean` | Archive parsing, lump lookup, map discovery |
| `Doom/Map.lean` | Vanilla map types, decoding, structural checks |
| `Doom/Automap.lean` | Pure diagnostic SVG rendering |
| `Doom/Fixed.lean`, `Doom/Bsp.lean` | Coordinate arithmetic and spatial queries |
| `Doom/Tables.lean`, `Doom/Angles.lean` | Exact trig tables and binary-angle operations with checked indices |
| `Doom/Assets.lean` | Palette/light tables, patches, composited textures, flats, sky selection |
| `Doom/Render.lean` | Camera spawn, software renderer, PPM output |
| `Doom/Controls.lean`, `Doom/Player.lean` | Free-camera controls and runtime WAD/input adapter for reference-tested walking |
| `Doom/Ticcmd.lean`, `Doom/Motion.lean` | Reference-tested keyboard commands, thrust, movement splits and friction |
| `Doom/PlayerPhysics.lean` | Reference-tested gravity, landing events, view height/bobbing, and isolated physics sequence |
| `Doom/Collision.lean`, `CollisionProbe.lean` | Ordered player position checks, static WAD wall diagnostic, and collision fixtures |
| `Doom/Move.lean` | Move acceptance/commit, ordered actor linking, immediate crossed-special callbacks |
| `Doom/Path.lean`, `Doom/Slide.lean` | Reference-tested ordered path intersections and three-corner wall sliding |
| `Doom/WorldPhysics.lean`, `tests/world_reference.py` | Connected collision/slide/player physics and independent C movement traces |
| `Doom/Pickup.lean`, `Doom/PlayerCounters.lean`, `PickupProbe.lean`, `tests/pickup_reference.py`, `tests/contact_reference.py` | Reference-tested pickups, live counters, metadata and runtime contact |
| `Doom/Things.lean` | Vanilla thing dimensions and idle frame sequences |
| `Doom/Random.lean` | Independent random streams, checked table lookup, isolation proofs |
| `Doom/Inventory.lean`, `Doom/Simulation.lean` | Pickups, use actions, doors, buttons, tick state |
| `Doom/SectorLights.lean` | Original lighting thinkers and walkover actions, topology and RNG integration |
| `Doom/Plane.lean`, `Doom/VerticalDoor.lean` | Original plane movement and vertical-door thinker kernels |
| `Doom/HeightClip.lean` | Original actor-height adjustment with effectful position queries |
| `Doom/Death.lean`, `Doom/DeathData.lean`, `Doom/DeathRuntime.lean` | Original kill/death actions, generated state chains and runtime corpse integration |
| `Doom/SectorChange.lean` | Non-crushing sector block traversal, corpse gibs and dropped-item removal |
| `Doom/ActorFlags.lean` | Generated original spawn health and sector-change actor flags |
| `Doom/Use.lean` | Original BLOCKMAP use tracing and action/side requests |
| `Doom/Scrolling.lean` | Original special-48 setup and scrolling-wall updates |
| `Doom/Status.lean`, `Doom/StatusBar.lean` | Original status rules, WAD widgets and palette presentation |
| `Doom/Replay.lean` | Script runner, state summaries, viewer status |
| `Doom/Weapon.lean`, `Doom/WeaponData.lean`, `WeaponProbe.lean` | Original fist/pistol/shotgun psprite actions, generated states and C comparisons |
| `Doom/Actors.lean`, `Doom/Combat.lean` | Enemy metadata, live weapon attacks and remaining prototype damage/AI adapters |
| `Doom/Sight.lean`, `Doom/Radius.lean` | Original BSP blast sight and radius damage requests |
| `Doom/Imp.lean`, `Doom/ImpRuntime.lean` | Original imp actions and live sight/movement/hearing integration |
| `Doom/Projectile.lean`, `Doom/ProjectileRuntime.lean` | Imp fireball spawning, flight, collision and explosion |
| `Doom/Hitscan.lean` | Original fixed-point autoaim, hitscan traversal and impact requests |
| `Doom/CombatView.lean` | Weapon overlay, health/ammo display, combat feedback |
| `Doom/Audio/` | DMX/MUS/GENMIDI decoding, original OPL2 driver, integer FM synthesis, effects and PCM mixing |
| `AudioProbe.lean`, `tests/audio_reference.py`, `tests/integration_audio.py` | Independent C audio comparisons and real E1M1 music verification |
| `Doom/Platform.lean`, `native/sdl.c` | SDL window/input/clock and PCM queue interface |
| `Doom/App.lean`, `Main.lean`, `Viewer.lean` | File I/O, commands, viewer loop |
| `Tests.lean`, `PlatformTests.lean`, `tests/` | Arithmetic, rendering, WAD, SDL tests |
| `FidelityProbe.lean`, `MotionProbe.lean`, `tests/fidelity_reference.py`, `tests/motion_reference.py` | Function-level Lean/C comparison harness and unobstructed motion traces |

Format references: id Software's published
[`doomdata.h`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/doomdata.h)
and [`w_wad.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/w_wad.c),
with artwork/pegging layouts checked against
[`r_data.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/r_data.c)
and [`r_segs.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/r_segs.c).
The thing metadata was checked against
[`info.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/info.c);
sprite rotation and movement conventions were checked against
[`r_things.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/r_things.c)
and [`p_map.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_map.c).
Door/switch/pickup behavior was checked against
[`p_doors.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_doors.c),
[`p_switch.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_switch.c),
and [`p_inter.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_inter.c).
Combat metadata and conventions were checked against
[`p_pspr.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_pspr.c),
[`p_enemy.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/p_enemy.c),
and [`m_random.c`](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/m_random.c).
The production engine runs Lean algorithms and does not link a C DOOM engine.
The separate fidelity test harness compiles selected upstream C routines as an
independent oracle. The BSP, RNG, checked-division, angle/table, ticcmd, motion,
player-physics, collision, and movement-commit ports carry upstream attribution
and GPL-2.0-or-later notices; the license is included in `COPYING.md`.
Audio ports also credit id Software, Simon Howard, Ben Ryves (MUS conversion),
and Alexey Khokholov (Nuked OPL3 1.8), under GPL-2.0-or-later. The audio reference
sources and exact revisions are recorded in `tests/reference/audio.json`.
