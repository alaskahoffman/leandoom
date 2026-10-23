# Engine roadmap

The compatibility target is vanilla DOOM and DOOM II, starting with single-player
DOOM 1.9 behavior. WAD loading is a necessary foundation, not evidence of gameplay
or demo compatibility. Each milestone should leave a runnable executable and
an independently checkable result.

## Agreed direction: idiomatic Lean with faithful behavior

Internal representations and code organization may change to suit Lean. Preserve
the arithmetic, rounding, timing, update order, random-call order, and historical
quirks that determine the original experience. Use explicit state and types to
make those requirements visible. Model observable effects of historical bugs in
controlled state where needed; reproducing unsafe C memory access is unnecessary.
Visual and audio fidelity require their own checks alongside simulation fidelity.

The initial behavioral target is ordinary DOS DOOM 1.9 single-player. Ultimate
and Final DOOM executable variants must be identified separately. Before calling
a comparison authoritative, record the reference revision/build, executable
variant, IWAD/PWAD hashes, options, and input/demo. The unchanged, hash-pinned
shareware 1.9 DOS executable is the final behavioral reference; a pinned Chocolate
Doom build provides broader diagnostic traces. Function-level references are pinned to Chocolate
Doom 3.1.1 (`410d96855b5df5410ff591a90efeafa889119224`) with source hashes and
compiler metadata in `tests/reference/`. Both full-engine reference builds and
the DOS executable/IWAD profiles are now pinned. The original-executable observer
currently covers level time, both RNG indices, player position, momentum and
angle, and selected imp/zombieman state-machine fields; it does not yet capture
the complete world state. See
[demo comparison](DEMO_COMPARISON.md) for scope and reproducibility.

These projects have complementary roles:

- [Chocolate Doom](https://github.com/chocolate-doom/chocolate-doom/blob/master/PHILOSOPHY.md):
  preservation philosophy, behavior, and compatibility research.
- [rust-doom](https://github.com/cristicbz/rust-doom): idiomatic language design
  and WAD/rendering implementation ideas. Its stated scope is an independent
  OpenGL renderer, with intentional differences from vanilla.
- [cpp-doom](https://github.com/lefticus/cpp-doom): a C++ fork of Crispy Doom 5.7.2,
  itself based on Chocolate Doom. Study language adaptation while distinguishing
  the inherited enhancements from the vanilla behavior we target.

Proofs should establish useful, explicit properties: parser bounds, index validity,
arithmetic correspondence, or preservation of a specified state transition.
An equivalence proof must connect to a justified reference model; proving a
property of an approximation does not establish fidelity. Current tests and
runtime checks are not formal proofs of engine equivalence.

## Current scope: E1M1 first

Prioritize features present in the pinned DOOM 1.9 shareware E1M1 before other
maps or DOOM II. `tests/integration_e1m1.py` inventories the actual WAD and checks
runtime scrolling, script partitioning, restart, relocated-start floor/lift crossings,
all three secrets and the exit switch. It runs in
`scripts/test-shareware`; this is a level-specific integration check, not a demo
or complete-level gameplay comparison.

| E1M1 feature | Map evidence | Current state |
| --- | --- | --- |
| Normal doors | Eight special-1 linedefs | Original use tracing and movement/clipping; activation-tic movement corrected, general thinker interleaving still pending |
| Exit switch | One special-11 linedef | Original normal-exit request and switch texture behavior checked; intermission/E1M2 transition pending |
| Fast lowering floor | One special-36 linedef, tag 1 | Original spawn/thinker rules and player-crossing/clipping integration checked |
| Repeatable lift | One special-88 linedef, tag 2 | Original spawn/wait/return/reversal rules integrated; repeat crossings checked |
| Scrolling walls | Eight special-48 linedefs, indices 352–359 | Original list/update behavior integrated and checked |
| Nukage damage | Four special-7 sectors | Original floor/clock gate and null-source damage integrated before use/fire and power counters; normal-spawn slime contact matches the comparison route |
| Secrets | Three special-9 sectors | Original floor-equality discovery and one-time counting integrated; all three sectors checked |
| Lighting | Specials 1, 8 and 12 | Original lighting kernels integrated; complete thinker order pending |
| Combat | Medium single-player: four zombiemen, two imps, six barrels | Original hitscan, supported deaths, barrel blasts, imp/zombieman scheduling, damage thrust and walking-actor/corpse momentum integrated; full damage metadata and thinker interleaving pending |
| Weapons | One single-player shotgun pickup | Original fist/pistol/shotgun switching and attack states integrated; seven pellets, one shell, WAD sprites and audio checked |
| Sound and music | Digital DS effects, GENMIDI and D_E1M1 | Lean effects mixer and nine-voice OPL2 music play in the viewer; original-C audio profile checked, whole-engine event timing still incomplete |

E1M1 also has shotgunners at higher difficulty. Its rocket launcher and chaingun
placements are multiplayer-only; they are not required for the current medium
single-player milestone. Corpse/decorative things and supplies already load, but
full original actor states/spawn timing still require work. Animated
textures/flats, menus and a validated end-to-end E1M1 run remain part of finishing
this level. E1M1 completion is not established by rendering all its geometry.

## Immediate work: establish fidelity before adding gameplay

The first-enemy E1M1 route now matches initialization and all 521 tics of the
original-executable profile and the broader Chocolate profile. The DOS observer
now includes enemy positions, XYZ momentum and signed health; it independently
detected the former tic-426 difference before monster thrust/motion was repaired.
The earlier tic-381 player damage mismatch is also fixed. The new 1,961-tic
`shotgun-secret` route extends that encounter through imp death, slime damage,
the second door, a lowering floor, secret supplies, shotgun pickup/auto-switch
and three blasts. It exposed missing floor damage at tic 1,249 and a collected
item retained as an inert scene slot at tic 1,828; both are fixed. All six
complete routes pass (5,383 tics plus initialization, including their shared
prefix), with repeatable original traces and deliberate corruption detection.
DOS schema v6 now directly observes health, armor, ammo, weapon selection,
weapon/flash state and countdowns, weapon XY, refire, extra light and secret count.
The shotgun route matches these additional fields; layout evidence is checked
against original instructions, with decoder failure tests and deliberate field
mutations. It also captures live imp fireballs and explosions: all six shots
and 414 projectile snapshots match the original executable, including position,
momentum, angle, floor/ceiling bounds, source, spawn `lastlook`, state/countdown
and missile flag. General pickup removal still uses the broader Chocolate profile.
The 2,445-tic `e1m1-exit` route continues through the final imp, a closing door
crushing its corpse, and the exit request. The latter is now captured directly
from DOS `gameaction`, with original instruction and relocation evidence. The
route exposed and fixed the corpse's stale death-state number at tic 2,243.
Next, port and compare `G_DoCompleted`/intermission and expand observation to
other spawned objects and their ordering. General
damage metadata, dynamic thinker interleaving and DeathThink remain incomplete.
The live enemy countdown has an all-32-bit correspondence theorem against an
operational reference, plus a conditional composition rule; state-entry actions
and whole-game correspondence remain unproved. See
[the encounter evidence and proof scope](DEMO_COMPARISON.md#first-enemy-encounter-and-local-correspondence-proof).

1. Pin the reference and build differential tests for integer/fixed arithmetic,
   lookup tables, BSP decisions, and RNG state. Investigate ambiguous overflow
   behavior against the reference instead of silently choosing a nicer rule.
2. Introduce vanilla tic commands and compare initialization and state after
   each tick, including momentum, actor states, update ordering, and RNG indices.
   Replace approximate movement, collision, and combat in dependency order.
3. Add original demo playback and regression coverage inspired by
   [Quickcheck](https://github.com/chocolate-doom/quickcheck) and
   [Statcheck](https://www.chocolate-doom.org/wiki/index.php/Statcheck).
   Matching end-of-level statistics is useful evidence, not proof of complete
   synchronization. Report the first divergent tick/field when traces are available.
4. Compare rendered frames and sound behavior separately, then expand weapons,
   monsters, and specials using the same fidelity checks.

The comparison harness now checks 788,115 cases: wrapping add/sub, fixed
multiplication, raw BSP side decisions, map-node conversion, both RNG streams,
supported fixed division, all trig table entries, fine-angle bin boundaries,
SlopeDiv, point-to-angle conversion, keyboard commands, thrust, horizontal/vertical
player motion, view-height recovery/bobbing, combined physics sequences, collision
geometry predicates, ordered position checks, move acceptance, actor relinking,
crossed-special callbacks, ordered path traversal, three-corner wall sliding,
connected player movement, runtime WAD/input adapter results, pickup grant rules,
touch effects, stateful pickup sequences, live player counters, power expiry
renderer colormap selection, and indexed high-detail fuzz columns
against independent C output.
Reference routine bodies are extracted
unchanged from hash-checked sources and compiled at both `-O0` and `-O2` with
`-fwrapv`; the harness checks integer widths, signed shifts, and narrowing behavior.
Offline tests use frozen outputs; `scripts/test-fidelity` rebuilds the oracle.
The BSP implementation now uses reference rounding and wrapping. Random lookup
bounds and stream isolation are proved, with no admitted lemmas. Gameplay random
call order remains approximate.

The exact sine (10240), tangent (4096), and arctangent (2049) values are generated
from pinned integer literals. Lean vectors encode the lengths, and Fin indices
prove every lookup is in bounds. Angle conversion retains unsigned slope
overflow, quantization, and octant-specific one-unit offsets. No host trig
function is used to regenerate the tables. The generated file is reproducible
with `scripts/generate-tables.py`; all prior 29,353 reference results are preserved.

`Fixed.divChecked` now has a kernel-checked equivalence proof against the original
DOS DOOM 1.9 routine bytes under explicit x86 semantics, for every input pair.
The wrapping `abs(INT_MIN)` guard is preserved; successful results, saturation,
and divide-error causes match. CPU divide errors become explicit Lean errors.
Addition, subtraction, multiplication, and arbitrary RNG call traces also have
binary parity proofs; see [the scope and reproduction guide](ARITHMETIC_PROOFS.md).
The viewer's movement/rendering still use their previous approximate arithmetic paths;
the new primitives will be integrated with the vanilla movement/simulation port.

Keyboard movement/fire/use now produces typed signed tic commands with the
original turn ramp, strafe/run constants, cancellation, and sideways clamping.
The horizontal motion port preserves turn-before-thrust order, forward-before-side
thrust, airborne restrictions, MAXMOVE clamping, positive-only split steps, and
the different rounding of division and arithmetic shift. Friction preserves the
strict stop threshold, active-command exception, and no-momentum cheat branch.
Lean proves a two-attempt bound for the unobstructed movement plan.

The C fixture extracts G_BuildTiccmd, P_Thrust, P_MovePlayer, and P_XYMovement
unchanged. It restricts input to keyboard movement/fire/use at full turn resolution
and motion to a live player with every P_TryMove succeeding. Unsupported collision
callbacks abort. Tests compare attempted positions as well as final state, all
8192 thrust directions, input combinations, signed command limits, and sustained
acceleration/release traces. These horizontal traces remain as independent regression
groups alongside the new vertical/view cases. All previous 134,292 golden results
remain unchanged.
The unobstructed fixture remains independent of the connected movement tests below.

The player branches of P_ZMovement and P_CalcHeight now match unchanged reference
routines: double initial gravity, floor-before-ceiling clipping, strict hard-landing
threshold and sound event, step-up view smoothing, height recovery, bobbing, and
the overwritten airborne ceiling clamp. Table indices are bounded by Lean's types;
these are tested behavioral ports, not formal equivalence proofs. View calculation
retains its caller-supplied onground value, and isolated tests also cover the
non-live recovery gate without claiming death-thinker coverage.

Combined fixtures follow P_PlayerThink/P_MobjThinker ordering: command thrust,
view calculation, XY motion, then Z motion only if off the floor or carrying
vertical momentum. The pinned P_Ticker source confirms player thinking precedes
the thinker loop. Tests cover complete drops/landings, ceiling hits, step recovery,
every bobbing phase, and raw arithmetic boundaries. The fixture records landing
sound events but has no audio output. Collision, reaction-time delays, sector/weapon
actions, animation ticking, and full thinker ordering remain outside these traces.

The collision foundation now covers P_PointOnLineSide, P_BoxOnLineSide,
P_LineOpening through contacted two-sided lines, both BLOCKMAP iterators, and
player P_CheckPosition with solid/inert actors and single-player pickups. It preserves the leading-zero
linedef, x-major/y-minor cell order, thing-list order, early-out prefixes, duplicate
line suppression, square thing contact, and equal-height ceiling-line ties.
The scene receives current actor links and destination sector heights explicitly;
the WAD adapter builds line geometry, while the static diagnostic obtains its
base sector from the existing BSP code. Unchanged C routines independently check
callback order and outputs. All prior 162,587 reference results are preserved.

The position-query stage itself does not commit movement, but does commit pickup
effects/removal. Actors with missile/skull effects are outside its type/domain. It rejects a ninth contacted special,
extended unsigned BLOCKMAP offsets/indices, unsupported signed dimensions, and
original DOS division faults. The loader records signed-offset compatibility while
retaining its existing diagnostic parsing behavior. Validcount rollover remains
unverified; the current query uses a fresh visited set. WAD integration fixtures
cover geometry conversion, exact wall tangency, the leading-zero quirk, and the
explicit unsigned-offset boundary. The viewer now uses these collision routines.

P_TryMove acceptance/commit and P_UnsetThingPosition/P_SetThingPosition now match
unchanged C routines on valid linked scenes. Tests cover exact height, step, and
dropoff boundaries, signed subtraction wrapping, flag exceptions, intermediate
floatok state, failures leaving actor/link state intact, and moves across cells,
sectors, and off-grid positions. Same-cell and zero-distance successes reinsert
the actor at list heads. NOSECTOR still updates the actor's subsector membership;
NOBLOCKMAP skips the block list. Corrupt linkage is rejected explicitly.

Crossed-special callbacks execute after relinking, in reverse contact order.
They re-read current actor positions and line special flags, preserving immediate
effects on subsequent contacts. Tests record events and use artificial callbacks
that disable lines or reposition actors; they do not implement DOOM special actions.
Handlers with nested position queries can overwrite vanilla's global spechit
scratch and remain outside this verified callback domain. The pure Lean move API
requires an explicit handler. All previous 176,007 reference cases are unchanged.

Path traversal and vanilla sliding now match unchanged C routines in bounded
solid/inert scenes. Divline predicates and intercept fractions retain their
own fixed-point rounding. Traversal preserves the boundary nudge, line-before-
thing order, first-inserted fraction ties, early exits, 64-iteration stalls, and
repeated thing hits. Tests reach exactly 128 intercepts; larger lists are rejected
until historical overrun behavior is established. Visitors are read-only.
Sliding preserves three-corner trace order, approach-margin rounding, quantized
projection, two retries, and Y-then-X fallback, including failed attempts that
retain changed momentum. Fixtures compare all trace/attempt/link state and
recording-only special crossings. All prior 187,018 reference cases are unchanged.

Collision/sliding now feed the horizontal movement and friction sequence, with
command thrust/turn and view calculation before body motion, and conditional Z
movement afterward. The saved split remainder survives a slide's momentum change.
Connected fixtures call actual unchanged P_TryMove/P_SlideMove from P_XYMovement,
checking all attempts, links, momentum, view/height state and recording-only
crossings. All prior 217,713 reference cases are unchanged.

Walking in the viewer and CLI now uses this sequence. The WAD adapter preserves
actor links between tics, mirrors external prototype actor/sector changes, and
keeps fixed body/view and keyboard state. Separate runtime fixtures compare WAD
and input-mask results with pinned C output. Unsupported profiles return errors;
there is no approximate movement fallback. Surrounding simulation actions remain
prototype behavior, so this is movement integration, not full-game fidelity.

Single-player pickup grants and P_TouchSpecialThing effects now match unchanged
C routines. Typed inventory dimensions keep four ammo classes, nine weapons,
six distinct keys and six powers; the port preserves body/player health updates,
pending weapon selection, difficulty amounts, dropped ammo, backpack behavior,
bonus and item counts, shadow flag, message IDs, and removal/sound decisions.
Fixtures cover all 36 pickup sprites, both commercial/noncommercial branches,
exact height boundaries, dead touchers, repeated pickups, full/overfull inventory,
and signed wrapping. The C fixture extracts constants from pinned p_inter.c,
d_items.c and deh_misc sources. All previous 254,267 reference cases are unchanged.

Pickup contact is now integrated into the movement core and runtime. Original
thing-list traversal calls the tested touch function before line/height checks;
consumption immediately unlinks an item while retaining the iterator's successor.
Inventory and removal survive later move rejection and slide retries. No-clip,
zero-motion, square contact and pre-step Z semantics are retained. Runtime map
flags/rendering and inventory mirror those effects; the old radial/visibility scan
and duplicate grant implementation are removed. Separate cards/skulls, pending
weapons, bonus/item counters and dropped-ammo flags survive the runtime bridge.
Original editor metadata and English pickup messages are pinned from info.c and
d_englsh.h. New contact/movement and metadata fixtures preserve all 308,467 prior
reference outputs. The runtime profile currently fixes medium skill and treats
MAP-prefixed maps as commercial.

Live-player power/counter ticking is now ported and used before movement pickups.
Berserk counts upward; nonzero timers and bonus/damage counters decrement with
signed wrapping; invisibility clears shadow only when its decrement reaches zero.
Fixed-colormap selection retains post-decrement blinking and invulnerability
priority over infrared. Runtime inventory preserves strength age and shadow;
live ticking is skipped for dead players and paused during inspection flight.
The C fixture compiles unchanged P_PlayerThink with inert movement/view/psprite
functions and a stubbed DeathThink. Counter and long expiry traces preserve all
324,315 earlier reference cases. This verifies the counter stage and early dead
return, not full PlayerThink or DeathThink.

Fixed colormaps now reach the textured renderer, including walls, masked posts,
planes, ordinary sprites, opaque weapons and muzzle flashes. Fullbright does not
bypass a fixed map; sky retains row zero. Effect row 32 is read directly instead
of clamping to normal lighting row 31. Missing inverse rows produce explicit
errors, while ordinary 32-row assets still load and render. Tests use nonstandard
COLORMAP bytes, palette lookup and patch overrides, checking first-tic timing,
blinking, expiry and transparency. The C fixture copies unchanged selection
blocks, with normal light rows supplied independently; it preserves all 361,801
prior comparisons. It tests selection rather than the original rasterizer.
High-detail fuzz rendering now uses the original R_DrawFuzzColumn and 50-entry
pattern, including inclusive spans, border clipping, COLORMAP row 6, mutable
neighbor reads and phase wrapping. The renderer retains palette indices alongside
RGB, draws background sprites before nearer fuzz sprites, and clips spectre and
invisible-weapon posts. Its phase belongs to presentations, not simulation tics;
it persists across frames and game restarts. Static exports start at phase zero.
The independent C oracle preserves all 366,793 prior comparison results. The
verified domain is stride 320, view origin zero, high detail and heights 3..200.
Full original projection/post rounding and BSP sprite visitation/tie order,
low detail and other view origins remain pending alongside the prototype combat
loop. Status palette selection is now ported, with a prototype damage bridge.

Map-spawned lighting specials 1/2/3/4/8/12/13/17 now use original flash, strobe,
glow and fire thinker rules. Two-sided adjacency determines minimum light; spawn
and tick order preserve their P_Random calls. Short light writes, bitmask delays,
synchronized strobes, glow endpoint reversal and fire's current-light/minimum+16
quirks match unchanged C routines. Special 4 retains its damage marker, without
claiming its still-unported damage behavior. Thinkers rebuild on restart and run
on simulation tics; presentation does not advance them. Runtime map light changes
feed COLORMAP selection. Snapshot JSON exposes light values, specials and timers.

The independent harness adds 34,708 lighting comparisons, covering all starting
RNG byte indices, mixed thinkers, supplied external RNG use, signed-light edge
cases, and adjacency. All 392,133 prior comparisons are unchanged. WAD integration
checks cover timing, RNG consumption, restart and pixels. General thinker ordering
and original actor-spawn RNG remain pending; prototype actors/doors surround the
verified lighting kernels. No full-map RNG, full-tic or framebuffer parity claim.

Walkover lighting specials 12/13/17/35/104/79/80/81 now run immediately in the
movement callback. One-shot clearing, repeatable actions, player-only eligibility,
tag zero, shared brightest-neighbor state, sequential writes, specialdata gating
and duplicate strobe insertion match unchanged original routines/case blocks.
New strobes share gameplay RNG and tick later in the crossing tic. Collision
special flags update immediately, preserving reverse contact order across multiple
triggers. The busy-sector adapter currently covers prototype doors only.
The harness adds 47,872 cases; all 426,841 previous cases are unchanged. Nine WAD
integration tests cover crossing directions, failed moves/use, immediate ordering,
strobe timing, repeats, duplicate thinkers, tags, restart and rendered changes.
General thinker interleaving and light use switches remain pending.

Moving-plane and vertical-door kernels now match unchanged `T_MovePlane` and
`T_VerticalDoor` bodies. Floors/ceilings in both directions preserve wrapping
16.16 steps, strict overshoot, tentative/restored-height callbacks and the
`pastdest`-despite-rollback quirk. All eight door types preserve countdowns,
reversal, removal and sound requests. Existing runtime door actions use these
kernels; exact-height arrivals now keep moving until the next overshoot tic.
JSON records per-tic thinker sound requests; the viewer now plays them.

The harness adds 57,930 comparisons; all 474,713 previous cases are unchanged.
WAD door states match frozen C traces for six normal/fast raise/open/close actions.
Non-crushing sector traversal/disposition is now integrated below. Crushing and
original activation/target selection still need ports. Doors-before-player
scheduling remains a prototype adapter. General thinker ordering/removal and map spawning of delayed
door types are pending; this is kernel parity and integration, not full-tic parity.

`P_ThingHeightClip` now uses the real effectful position query in tentative and
rollback door callbacks. It preserves on-floor equality, forced airborne lowering,
wrapped arithmetic and the ignored position-query return. Non-player queries
honor monster-blocking lines. Height changes and pickup effects survive callbacks,
so door updates can collect items while the player stands still. The oracle adds
5,728 comparisons, including real query/collection effects and rollback sequences;
all 532,643 previous cases are unchanged. Four WAD integration tests cover idle
collection, obstruction, monster-line early returns, restart and segmentation.
Non-crushing sector traversal and corpse/drop disposition are now ported below;
crush damage and blood remain pending.

`Doom/SectorChange.lean` now uses original expanded sector block bounds,
x-major/y-minor traversal and live successor links. Dead non-fitting actors become
zero-size, non-solid gibs; dropped items are removed; other shootable actors
obstruct the move. Solid decorations alone do not obstruct it. Original spawn
health/flags for 118 actor types distinguish map corpse decorations from kills.
Runtime doors retain clipping/disposal effects across rollback, render `POL5A`
gibs, and expose gibbed/removed-drop indices without awarding pickups.

The oracle adds 3,687 comparisons from unchanged C routines/metadata expressions;
all 538,371 previous cases are unchanged. Five WAD regressions cover expanded
block scans, corpse/drop policy, reset/partitioning and gib rendering after
reopening. Two Lean checks cover sector bounds assembly. Damage/blood spawning,
full state/lifetime behavior, and original thinker scheduling remain pending.
The new API explicitly handles only `crunch=false`; prototype combat still
supplies runtime damage; supported deaths now use the original kill/state routines.

Use tracing now follows original `P_UseLines`/`PTR_UseTraverse`: fine-angle
endpoints, BLOCKMAP membership, original tie order, opening tests, first-special
stopping and original side classification. E1M1's eight scrolling lines now use
the original fixed list and wrapping one-unit-per-tic updates, after map thinkers.
The oracle adds 9,351 comparisons; all 542,058 earlier cases are unchanged.
Five runtime scrolling tests check shared sides, front-only changes, overflow,
restart/partitioning, rendered pixels and special-48 interception of a use press.
Original range/BLOCKMAP behavior also corrected two older use fixture assumptions.

E1M1 floor 36 and lift 88 now use `Doom/FloorMover.lean`: original four-unit
speed, neighbor searches, one-shot/repeatable crossing rules, busy-sector and
nonplayer/projectile gates, 105-tic wait, strict endpoints, blocked-ascent reversal
and the 30-platform limit. Player movement dispatches crossings immediately;
actual sector clipping moves riders and pickups and preserves rollback effects.
Sound requests are recorded and now played by the audio-enabled runtime. The oracle adds 43,432
comparisons against original thinker routines and selected unchanged spawn/crossing
branches; all 551,409 earlier comparisons remain unchanged. Seven WAD tests cover
runtime timing, riding, obstruction, busy targets, retriggering and restart.

The shareware integration relocates only player one's start while retaining E1M1's
original geometry/BLOCKMAP and other things. Crossing line 308 lowers sector 59
from 96 to −40; crossing line 195 takes sector 70 from 104 to −48 and back to 104.
This does not establish a complete run from the normal start. Monster crossing
dispatch, manual door use on an active platform, and full original thinker
interleaving remain pending.

`Doom/LevelSpecials.lean` now counts initial secret sectors and implements original
case-9 discovery: exact sector-floor equality, signed counter increment and
clearing the sector special. Live-player checks precede XY/Z movement, so entry
or landing is observed on the following tic. Normal exit switch 11 uses the
original texture-list precedence and one-shot clearing-before-sound quirk, then
queues completion even without a texture match. Base archive markers select the
normal game-mode switch list; patch markers do not override it.

The activation tic finishes, then gameplay holds at the explicit pending
completion boundary. `G_DoCompleted`, original intermission UI/timing and E1M2
loading remain unimplemented. Other switch adapters, historical button sound origins and complete PlayerThink/use
ordering remain pending. Nine runtime tests and 12,500 C comparisons cover this
work; all 594,841 earlier comparisons remain unchanged. Real E1M1 checks relocate
only the start to discover sectors 68/69/70 and activate line 330, including its
`SW1STRTN` → `SW2STRTN` texture change and restart.

Current priority is E1M1 combat: original damage/thrust/pain actions, weapon states
for the remaining weapons, enemy sight/AI, and global thinker ordering. Imp
actions and fireballs now have the separately verified implementation below.
Completion/intermission/E1M2 handoff and door activation remain later work. These still require the remaining special handlers
(including reentrant scratch semantics),
animation/state ticking, reaction-time gates and complete thinker ordering.
Unsupported pending weapons, general
thinker deletion and item respawn remain separate dependencies; the remaining
prototype combat/inventory bridge does not establish their original timing.
Pickup effects must preserve their position-check timing. Ticcmd demo
encoding/turn quantization for recording, mouse/joystick, remaining weapon/special
commands, full-state coverage, and image comparisons remain pending. The
[demo comparison harness](DEMO_COMPARISON.md) now decodes a bounded vanilla E1M1
profile, runs direct tic commands through both engines, and reports initial/per-tic
differences in selected fields. The pinned movement, stationary-fire and moving-fire
cases match their declared fields against both references. Live impact tracing
exposed and verified a fix to player action/movement ordering: turn/thrust and
view, then use/fire and counters, then XY/Z and pickups. General thinker ordering
and complete-demo synchronization remain pending. DOS `FixedDiv`
INT_MIN behavior is now covered by the arithmetic binary proof.

Existing fixture tests remain useful for parser safety and prototype regressions; expectations
that encode simplified gameplay must change when reference evidence contradicts
them. The implementation milestones below describe the prototype's existing
capabilities, not completed vanilla-compatibility milestones.

## 1. WAD and map foundation — implemented

Read archive directories, apply ordered PWAD overrides, load the ten vanilla map
lumps, reject invalid structural references, and export a diagnostic automap.

Evidence: generated fixtures and all 68 Freedoom 0.13.0 maps. Test the user's
original DOOM/DOOM II WADs when available.

## 2. First-person geometry — implemented as a diagnostic viewer

Implemented 16.16 camera coordinates, wrapping binary angles, and tests for signed
rounding, overflow, multiplication, and checked division. Projection deliberately
uses floating point for this milestone. Arithmetic and projection must be aligned
with vanilla's exact behavior before claiming demo/pixel compatibility.

Implemented BSP point-to-subsector lookup and front-to-back traversal, projection,
near-plane clipping, one-sided walls, two-sided portals, upper/lower spans, and
flat-colored floor/ceiling regions in a 320×200 software framebuffer. PPM output
and an SDL2 window use the same pixels. The native adapter contains no map,
rendering, collision, or gameplay algorithms. The macOS viewer runs on the OS
main thread to meet AppKit's requirements.

Evidence: rendered Freedoom E1M1 and all other 67 player-start views; independently
checked portal projection, closed-door occlusion, back-side views, and clipping
on a generated two-room fixture. Native presentation and dummy-driver lifecycle
checks pass. Movement controls are unit-tested; the unbundled executable was not
accessible to the UI automation tool for live keyboard testing. Free camera
movement is a renderer test, not player physics. Original commercial assets and vanilla image comparisons remain pending.
Static sprites are now implemented in milestone 3. Texture work is tracked below.

## 3. WAD artwork and lighting — textures and idle sprite animation implemented

Implemented PLAYPAL, COLORMAP, PNAMES, TEXTURE1/2, column/post patches, clipped
patch composition, flats, and sky selection. Resource overrides work across
archives. Palette index 255 is a valid opaque color, and transparency is tracked
separately. All decoding and rendering remain in Lean.

Walls now use the original unsigned angle clipping and fixed-point projection,
scale interpolation per visible segment fragment, 20.12 edge accumulators,
texture-column tangents and reciprocal vertical sampling. Floors and ceilings
collect visplanes, split overlapping column ranges, and enumerate horizontal
spans. The flat drawer reproduces R_DrawSpan's packed 6.10 coordinate arithmetic,
including the carry from the low half into the high half. Sky sampling retains
the original screen-angle table and 128-row wrap. The world renderer supplies
integer distances/scales to the existing lighting tables. Sprites now use the
original fixed transform, rotation and patch-origin rules, post clipping, saved
wall silhouettes and stable scale sorting. Masked walls interleave with sprites
instead of depending on a depth buffer. BSP back-child bounding boxes are tested
against the solid-column list. The weapon overlay retains its half-unit midpoint.

Texture and flat animations use directory order, absolute resource-index phase,
eight-tic cadence and the pre-increment level clock. The single-patch texture
column path ignores vertical placement offsets, reproducing the SKY1 -8 quirk.
Opaque sampling keeps the original patch data pointer, including padding bytes at
short-wall edges. The compositor shortens negatively clipped posts without moving
the source pointer. Passive sprites use the randomized first spawn countdown.

Evidence: the previous wall/plane/light/sky tests plus 4,590 sprite projection,
post clipping and animation cases against extracted original C at both `-O0` and
`-O2`. Integration checks cover nonstandard animation member names, tick boundaries,
restart, missing endpoints, texture fast-path/compositor differences, mirrored
origins, silhouette clipping and equal-scale sprite ties.

`scripts/compare-render` remains unchanged. All seven repeated matched-state
`e1m1-exit` samples and the independent sky-window sample now have zero differing
pixels, including their status bars. The last route pixel came from NUKE24 post
padding; the window sample's 177 differences came from TEKWALL1 compositing and
an armor bonus's initial animation phase. An additional 61 composite-column cases
match extracted R_DrawColumnInCache at both `-O0` and `-O2`; framebuffer tests cover
the padding read and spawn animation boundaries, partitioning and restart.
Artifacts: `artifacts/render-tightened-final` and
`artifacts/render-tightened-sky-final`. The reference remains pinned Chocolate
DOOM; this is neither original DOS video nor a rendering equivalence proof.
Remaining work includes broader frame coverage, general render-only effect
insertion history, non-power-of-two texture widths and original overflow behavior.

Pickup HUD text now renders with the original WAD font at (0,0), uppercasing,
four-pixel spaces, patch offsets, right-edge termination and 140-tic lifetime.
Framebuffer tests cover font posts/spacing, expiration, sector-lit weapons and
world brightening during a pistol flash. Message toggle/recall and chat remain
outside this single-player pickup-message path.

Evidence: 16 artwork test groups, 36 total Lean checks, and textured player-start
renders for all 68 Freedoom maps. Pixel assertions cover composition, transparent
posts, independent slanted-wall ray intersections, pegging, floor projection,
palette/light remapping, and sky portals. Standalone asset exports support inspection.

Map things now use 115 vanilla editor-number definitions, spawn frames,
rotation-zero or eight-direction sprites, mirrored paired lumps, patch origins,
floor/ceiling placement, and fullbright flags. Single-player medium-difficulty
things are selected. Per-pixel depth resolves sprite overlap with walls, planes,
and masked midtextures. Unknown/custom types and invisible map markers are omitted.
The metadata is based on id Software's published
[info.c](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/info.c);
no original engine algorithms are compiled or linked.

Idle cycles now use per-frame vanilla durations and fullbright flags. All needed
frames load before interactive simulation begins, with per-archive sprite namespaces
and standalone PWAD replacements. Initial idle cycles are synchronized; AI/actions
and randomized spawn delays are not emulated.

Remaining: actor behavior, texture animations,
exact vanilla projection and rasterization; reference-engine image comparisons
now expose the remaining differences.
The default viewer is textured; headless `render-flat` retains geometry diagnostics.

Acceptance: recognizable original E1M1 views using user-supplied assets, with
image comparisons against a reference engine at fixed camera positions.

## 4. Deterministic simulation — reference-tested player movement integrated

A 35 Hz walking loop now runs independently of presentation. Radius/height
collision, blocking linedefs, portal headroom, 24-unit steps, gravity, solid map
things, original split movement, sliding, momentum/friction and view recovery
now use the reference-tested Lean core. The surrounding simulation still needs
faithful action and thinker ports before demo compatibility. A headless
`walk` command supports fixture tests. F toggles inspection flight, returning to
the previous valid walking position when disabled.

Evidence: independent collision fixtures include a slanted wall, fast motion,
portal flags, headroom, steps, drops, and solid versus non-solid things. Sprite
fixtures check offsets, eight rotations, mirroring, transparency, depth, lighting,
and archive overrides. Current total: 355 Python groups and 80 Lean checks; all
nine DOOM shareware maps render with combat, and the SDL viewer smoke passes.
Earlier Freedoom validation covered 68 maps, plus 35 forward-input and 20
coasting tics on each map without errors, collecting 26 items across those routes.

Remaining: other special handlers, complete player/actor state ticking,
and exact gameplay random-call order. Walking now respects original BLOCKMAP
lists, including omissions. Test-room BLOCKMAPs cover their full geometry;
the previous prototype's full-linedef scan had hidden those fixture omissions.

Acceptance: scripted movement through a test map containing corners, stairs,
narrow openings, and ledges produces repeatable state hashes. Define the exact
compatibility policy for overflow and historical engine quirks before claiming
demo synchronization.

## 5. A complete level — first combat loop implemented

Implemented use rays, manual/keyed doors, tagged door switches and buttons,
SW1/SW2 texture changes, opening/waiting/closing ceilings, and obstruction checks.
The player and solid actors prevent closing doors from crushing them; collision
and rendering read the same updated sectors. Supported linedef numbers are listed
in the README; unsupported use specials report their number instead of pretending
to activate.

Implemented key colors (cards or skulls), health/armor caps, ammo/backpack capacity,
weapon ownership/ammo grants, and power-up inventory/timers. Collected actors are
removed from the scene. Pickup visibility is checked against closed geometry.
The fist, pistol and shotgun work; armor and invulnerability protect the player. Other weapons
and most power-up effects are not connected yet.
Window-title feedback makes key locks, pickups, and inventory visible.

Evidence: interaction fixtures, a reusable three-room lab, scripted JSON snapshots,
rendered switch/pickup assertions, all 68 Freedoom maps at tick 35, and the native
SDL viewer. The shared simulation drives both the interactive and scripted paths.

The initial combat roster includes zombiemen, shotgun enemies, and demons. They
acquire targets using facing/line-of-sight checks, pursue with collision, attack,
react to damage, and die. Corpses stop blocking movement; human enemies drop
collectible clips/shotguns. The player has a fist, pistol and shotgun, WAD weapon frames,
health/ammo readouts, hit/damage feedback, death, and a full reset. Shots now use
original fixed-point autoaim/hitscan; non-imp sight still uses the prototype portal ray.
Actor updates use a stored vanilla random-table index, but simplified decision
rules and call order are not demo-compatible.

Evidence: combat fixtures check first-shot damage, repeated-fire timing, nearest
hits, walls and lintels, armor, invulnerability, hearing/ambush, drops, corpse
collision, death/restart, WAD pose/weapon pixels, and repeatable script segments.
All 68 Freedoom maps render after 35 combat ticks; native presentation checks pass.
The existing interaction scripts retain passive actors for focused diagnostics.

`Doom/Hitscan.lean` now provides original aim/shoot callbacks over the reference-
tested BLOCKMAP traversal. It preserves actor-diagonal intersections, ordering,
portal slope clipping, shootable/self gates, signed midpoint rounding, 1024-unit
center/side autoaim retries, 2048-unit shots, impact offsets and sky rules. Live
pistol/enemy hitscan calls share that path. Solid decorations no longer absorb
shots merely for being solid. Ordered special/puff/blood/damage requests are
visible in replay JSON, while action effects remain the existing combat bridge.

24,063 new C comparisons and eight runtime regressions verify this boundary;
all 607,341 previous C results remain unchanged. Real E1M1 geometry checks hit
zombieman 87 and barrel 35 using relocated starts. The enlarged combat fixture's
BLOCKMAP now covers its true bounds. Blood/puff actor spawning and RNG/lifetimes,
P_DamageMobj, non-imp monster sight/AI, full player/thinker ordering
and other projectile attacks still need original ports. Supported weapon states
and shotgun firing now use the separately checked port below.
Imps/barrels now take damage; original barrel radius attacks are integrated below. Shoot-specials
24/46/47 fail explicitly when applicable until effectful callbacks are implemented;
E1M1 contains none. This is hit-selection parity, not combat or full-tic parity.

`Doom/Death.lean` now implements original `P_KillMobj`, `P_SetMobjState` for the
selected death tables, `A_Scream`/`A_XScream`/`A_PlayerScream`/`A_Fall`, and finite
state countdowns. Generated player/zombieman/shotgunner/demon chains retain exact
frames, durations and transitions. Signed health drives the strict extreme-death
threshold. Kill credit/frags, player-dead state, first-frame RNG shortening, corpse
flags and quarter-height bodies are retained. Death does not relink the actor or
replace it with a map decoration. Monster solidity ends at `A_Fall`; player
solidity ends immediately. Drops preserve item-spawn RNG consumption and dropped
pickup semantics. Sound/weapon/automap actions are explicit requests.

Evidence: 17,728 new independent C comparisons at both optimization levels, with
all 631,404 prior results unchanged; ten runtime tests for thresholds, original
frames/actions, collision, drops, player death and reset; real E1M1 pistol death
and final corpse/drop checks. This stage brought the total to 649,132 comparisons in 72 groups.
The oracle stubs drop/weapon/automap callees while checking their request order;
it is not a full thinker or spawning oracle. General P_SpawnMobj, actual weapon
lowering and DeathThink, corpse momentum/physics, nightmare respawn and additional
monster death chains remain pending; imp/barrel chains are now covered below. Full damage, impact effects and
weapon-state behavior are the next combat dependencies.

Imps now use 60 health, pain states and original normal/extreme death chains.
Barrels use 20 health, stay idle after surviving damage, and execute A_Explode on
the original BEXP4 entry. They remain solid until final S_NULL removal; chains
retain each barrel's death delay. Barrels grant no monster kill and no drop. The
first surviving hit assigns the remembered source; a lethal hit does not retarget.

`Doom/Radius.lean` implements original blast block order, wrapped bounds, radius-
adjusted Chebyshev falloff, shootable/boss gates and ordered damage requests.
`Doom/Sight.lean` implements the DOOM 1.9 BSP/REJECT sight path used from each
victim toward the quarter-height barrel, with original portal slope rules and
horizontal-side typo. It does not substitute the prototype enemy sight ray.

Evidence: 75,105 new C comparisons at -O0/-O2 (77 groups / 724,237 total), ten runtime
regressions, and real E1M1 pistol kills of imp 8 and barrel 35. All 649,132 earlier
comparisons are unchanged. Sprite preloading includes all imp extreme frames and
fullbright barrel explosions. Imp AI and fireballs are now covered below.
Full P_DamageMobj/thrust, general thinker
interleaving and relocating/reentrant blast damage callbacks remain pending.
The existing damage adapter does not move targets or trigger instantaneous nested
blasts, so ordered radius requests can be applied sequentially in this domain.

Imp live behavior now uses original normal-speed single-player `A_Look`, `A_Chase`,
`P_NewChaseDir`, range checks, `A_FaceTarget` and `A_TroopAttack`, with generated
original live/pain/fireball state tables. Runtime uses BSP sight, fixed-point
BLOCKMAP movement, persistent sector hearing/ambush rules, manual-door gates and
real imp fireballs. Fireballs retain spawn timing/half-step, shadow aim, species
immunity, contact damage, flight and fullbright flight/explosion rendering.

Evidence: five new C groups / 63,878 cases, **82 groups / 788,115 total**;
all 724,237 earlier results unchanged at `-O0`/`-O2`. Eleven runtime tests cover
state timing, sight/hearing, melee, travel/dodging, walls, doors, reset and rendering.
Real E1M1 checks include imp fireball spawning and geometry impacts.
Fast/nightmare/multiplayer, full P_DamageMobj thrust/general infighting, other
actor spawn RNG and original general thinker ordering remain pending.
Projectiles update in creation order after actors; manual door allocation still
uses the existing adapter. This does not establish whole-tic or demo parity.

Remaining: full vanilla thinker/actions, other projectile attacks, remaining monsters,
the remaining player weapons, infighting, other floor/lift kinds,
remaining walk-over triggers, exits, and the remaining original HUD/menu screens.
Audio decoding, sequencing, FM synthesis and mixing are now in Lean; SDL queues PCM.
See the audio milestone below for its reference profile and remaining limits.

Acceptance: start E1M1, fight enemies, collect items, use doors, die/restart,
and exit to E1M2. No scripted substitute for actual level logic.

### Fist/pistol/shotgun selection and attack states implemented

Keys 1/2/3 select the fist, pistol and owned shotgun. New shotgun pickups auto-equip
through original lowering/raising actions; pending switches wait through the pump
sequence and suppress refire. Exhausted shells fall back to pistol ammo, then fist.
The fist includes melee range, random/berserk damage, impact sound and target facing.
The shotgun spends one shell for seven sequential hitscan pellets, sharing autoaim
but drawing each pellet's damage/spread immediately before its hit effects.

`Doom/Weapon.lean` uses generated original psprite tables, the weapon-before-flash
countdown, original ready/lower/raise/refire actions and bob positions. WAD shotgun,
flash and fist patches, weapon audio, and active status ammo are connected. The
old pistol timer's extra ready-delay tic is corrected. A separate C corpus in
`tests/reference/weapons.json` compares **68,480 commands** at `-O0`/`-O2`, covering
state/flash timing, positions, ammo, refire/latch, death, sound/shot requests and RNG
with supplied damage callbacks. Ten additional tests bring the main suite to
**354 Python groups and 80 Lean checks**. The earlier 788,115 gameplay comparison
cases and audio corpus remain unchanged. Real shareware E1M1 checks exercise its
actual shotgun pickup, seven pellets/one shell, and pistol reselection.

Remaining boundaries: the existing map-start adapter starts at ready rather than
`P_SetupPsprites`; global player/mobj/thinker ordering, full damage, blood/puff actor
spawning and RNG, and other weapons remain unfinished. Extra-light state is ported
and traced, but world lighting does not consume it yet; muzzle-flash artwork is
fullbright. Unsupported weapon pickup requests remain stored without equipping.
These are routine/integration comparisons, not full-combat or demo parity.

### E1M1 audio implemented; whole-engine timing still incomplete

`Doom/Audio/` decodes DMX digital samples and MUS/GENMIDI, implements the original
DOOM 1.9 nine-voice OPL2 driver, and ports the integer melodic OPL2 path of Nuked
OPL3 1.8 to Lean. Effects use the original eight-channel allocation/priority,
origin replacement, distance/stereo and miscellaneous-RNG pitch rules. Gameplay
emits sounds at its existing action sites, including original imp/death actions,
fireballs, barrels, pickups, doors, switches and movers. Removal stops an emitter.
SDL only opens and queues the 44,100-Hz stereo PCM device; no native synthesizer
or external soundfont is required. Restart resets playback; `--no-audio` disables it.

The separate pinned `tests/reference/audio.json` corpus checks unchanged C MUS,
OPL-driver, sound-spatialization and channel routines at `-O0`/`-O2`, plus 168,128
stereo frames against Nuked. Real shareware E1M1 checks all 5,828 score events,
the complete register trace and 220,500 PCM frames. Twenty audio tests brought
the suite to 344 Python groups and 80 Lean checks at that milestone; the 788,115 gameplay comparison
cases remain unchanged. `scripts/test-shareware` includes the real score check;
`scripts/test-audio-reference` rebuilds the independent C corpus.

This establishes an explicit software profile, not DOS hardware or demo parity.
It uses immediate OPL writes and exact 140-Hz MUS loops without Chocolate Doom's
5-ms restart guard. SFX interpolation and measured DMX pitch approximation remain
backend choices. Full sound-event ordering awaits the remaining thinker/AI ports;
non-imp alert variants/cadence and player pain timing remain prototype behavior.
OPL3, PC speaker, external MIDI, linked chaingun sounds, E4 music remapping and
volume controls remain separate work. Details and playback/export commands are
in [the README audio section](../README.md#e1m1-sound-and-music).

### Status bar implemented; remaining original HUD and menus

Combat now uses the original single-player 320×32 WAD-backed bar below a
320×168 view. Health/armor percentages, active ammo, four ammo/max-ammo totals,
weapon ownership, card/skull keys and the face replace the development text and
crosshair. Skull icons replace cards; ready-weapon ammo does not follow a pending
pickup. Switching the supported weapons updates the readied ammo type at the
bottom of the lowering sequence, including the E1M1 shotgun pickup.
Offsets, transparent posts, resource overrides and original widget drawing order
are supported. Full refresh is used; incremental dirty-region behavior for unusual
custom patch overlaps is not claimed. DOOM 1.0 split bars and multiplayer/frags are
outside the supported profile. With STBAR present, missing UI art or fewer than
14 PLAYPAL palettes is an explicit load error; UI-less fixtures remain diagnostic.

Face state now follows the original priorities/timing, damage direction, pickup
grin, held firing, invulnerability and death. One M_Random call occurs per combat
tic, after gameplay, independently of frame count and P_Random. The original
ouch sign bug and persistent timers across ST_Start are retained. The C oracle
checks 10,304 face sequence steps with supplied attacker angles; the runtime uses
the separately verified fixed-point angle core. This does not establish whole
P_DamageMobj/DeathThink or thinker/ticker parity around the prototype combat loop.

PLAYPAL selection now covers damage, bonus, berserk and radiation-suit blink over
the whole indexed frame, including the bar. The prototype damage bridge remembers
the attacker and updates damageCount; the full damage routine remains work; supported kill/death-state routines are now ported.
The 22,516 new C cases cover numbers, palettes, faces and ready-ammo/key selection;
all 369,617 prior cases are unchanged. Pixel tests cover all 64 card/skull masks,
armor/weapon pickups, active-ammo ownership, digits and patch offsets, face timing,
death/invulnerability, palette application and fuzz at the 168-row view border.
DOOM shareware 1.9 is now the primary development/preview asset set. The original
archive and WAD are SHA-256 pinned in `tests/reference/shareware.json`; all nine
Episode 1 maps validate and render after 35 combat ticks, and the SDL eight-frame
smoke test passes. `scripts/viewer` defaults to its E1M1 and `scripts/test-shareware`
repeats this check offline. The original archive/readme and extracted WAD remain
local, under ignored artifacts. Freedoom's 68-map corpus remains secondary
compatibility coverage; registered/commercial IWADs are still user-supplied.
This asset switch does not establish original executable/demo or pixel parity.

Next UI work: original HUD message font/placement and timing, menus, configurable
view sizes, then intermission/finale screens as their game transitions are ported.
Preserve original input ordering and tic timing, with independent source checks
and WAD pixel fixtures. Full-game and DOS framebuffer parity remain separate targets.

## 6. Compatibility and performance

Expand to all DOOM/DOOM II level specials and actors, menus, intermissions,
save/load, and demo playback. Differentially test against a designated vanilla
reference, tracking the first divergent tick and state field.

Acceptance: a published compatibility matrix, reproducible demo results, and
frame/tick benchmarks on named hardware. Profile Lean before optimizing; preserve
Lean ownership of the engine algorithms. Multiplayer and extended source-port
formats come after the single-player compatibility target.

## Using Lean's strengths

Keep parsers fallible and the simulation state explicit. Start with useful local
invariants: validated array indices, framebuffer bounds, nonzero divisors, and
bounded BSP traversals. Add proofs where they eliminate real failure modes.
The RNG module proves lookup bounds and stream isolation, and the binary proofs
establish core arithmetic and RNG trace parity under documented x86 semantics.
Other systems still rely on runtime checks and tests. This is not a formally verified engine.
Neither a proof of bounds safety nor successful WAD parsing
establishes behavioral equivalence to DOOM.
