# E1M1 observable correspondence: initialized-state boundary

## Active user-approved scope (supersedes historical startup TODOs)

The proof begins at explicitly corresponding initialized pinned DOS and Lean
E1M1/HMP states. Launch, OS/filesystem and VGA initialization proofs are optional
frozen foundations, not prerequisites on the active critical path. Prefer real
captured, pinned and checked state over fabricated fixtures. State provenance is
an explicit empirical/trusted boundary, not a proof of boot-to-game execution.
The immediate task is a checked initial relation connected to production
`Engine.start` and existing aiming input predicates, followed by preservation
during admitted gameplay. Do not assume future matches, successful queries,
per-call contracts or preservation. Preserve raw heap/render/video state and
record the precise boundary relative to first presentation and opening wipe.

The first exercised slice is now recorded in
[INITIALIZED_E1M1_BOUNDARY.md](INITIALIZED_E1M1_BOUNDARY.md): authentic pre-first-
P_Ticker RAM/VRAM capture, production Engine.start projection, checked map/actor/
ordered-list/RNG/stamp data and kernel input/freshness bridges. Full initial
equivalence, address refinement, first-gameplay-aim-entry transport, remaining
aim contracts and gameplay preservation are still open. The historical startup
sections below are preserved references, not the active TODO list.

The goal is equality of observable behavior for every admitted input sequence
from the pinned shareware E1M1/HMP setup. No whole-tic DOS-to-Lean theorem has
been completed. Local routine proofs, deterministic replay, and zero-difference
recorded runs are useful evidence and components, not that theorem.

This plan supersedes allocator expansion as the immediate work priority. The
chronological detail remains in [E1M1_PROOF_SCOPE.md](E1M1_PROOF_SCOPE.md).

## What the final argument must connect

1. Establish a relation between the initialized original machine and the full
   live `Engine.State`. The relation may abstract registers, temporary storage,
   and data representations, but must retain everything that can affect future
   observations, including RNG, thinker order, render history, and relevant heap
   contents. This is an open obligation, not a supplied equivalence axiom.
2. From related reachable states and the same admitted command, prove that a
   complete update/presentation cycle produces equal observations and related
   successor states. Include exit and failure behavior; do not exclude a path
   merely because it disagrees. Intermediate machine calls need not correspond
   one-for-one to Lean calls.
3. Compose that result over arbitrary finite input prefixes. The existing
   interaction replay theorem connects the actual Lean engine to its interaction
   interpretation. It does not yet provide the DOS side or step 2.

The first claim is the existing **silent, one-frame-per-tic profile**: gameplay
observations, exact RGB presentations, and level-exit behavior. Matching logical
sound events would be an additional claim; matching sound/music samples also
requires the mixer/synthesizer, output schedule and original sound configuration.
The current `Engine.Presentation` has no audio output. Thus proving the current
interaction model alone cannot establish “sounds the same.”

## Connection map

| Obligation | Reusable work | Still needed for the complete tic |
| --- | --- | --- |
| Initial related states | Fixed binary/WAD profile, local map-loading/startup proofs | One assembled initial-state relation, including invariants relied on later |
| Input and player preparation | Original movement, view-height, floor, selection and use-gate segments | All reachable branches joined to the production player stage; fresh-use geometry/action dispatch |
| Weapon update and its effects | Original psprite, flash, ready, ammo and firing segments | Production action callbacks and their event interpreter, full weapon/player observations, preserved caller/reachable-state invariants |
| Actors and world changes | Local damage/death, RNG and sound-traversal proofs | Actual thinker ordering and all reachable actor, projectile, door, floor and collision effects |
| Render and present | Original-byte arithmetic, live pixel-difference harness, production pure engine wrapper | Rendering correspondence for related states: walls/floors/sprites, lighting, HUD, palette, fuzz, video pages and observable heap effects |
| After presentation | Explicit `Engine.afterPresent` opening-wipe behavior | DOS correspondence for its RNG, heap and video-page changes |
| Arbitrary prefixes | `interaction_replay_sound` and `interaction_replay_iff` | Original execution model at the same boundary, initial relation, complete one-cycle preservation and observation equality |
| Audio extension | Live SFX/music implementation and reference tests | Formal observations plus event ordering and the selected DOS audio backend/sample semantics |

This is a dependency map, not a percentage-complete estimate. Internal equality
is needed only insofar as it supports future observable equality. For example,
asset overreads can expose heap contents, so some memory facts matter; this does
not make a complete allocator proof the automatic next task.

## First runtime connection after the priority change

`Doom/Proofs/E1M1WeaponRuntime.lean` reuses the existing weapon/flash theorem and
connects it to `Simulation.weaponTick`, which the actual alive/dead player paths
call. `Simulation.weaponContext` now exposes the unchanged production input
construction; no alternative game implementation is introduced.

The new guarantees are:

- Under the quiet-weapon branch condition, the original instruction segment
  starting at the first psprite slot reaches the same five flash fields that the
  live simulation installs: state pointer, timer, extra light, and coordinates.
  All supported flash countdown/expiration cases remain included. The theorem
  inherits the original initial-memory, table and separation contracts.
- The real event handler has no events to execute on that branch. A full Lean
  state-update description shows what it installs and preserves; corollaries
  explicitly preserve RNG, audio state/events, noise targets, shot count and errors.
- Supported flash states stay supported at this runtime boundary.

Limits: this does not prove the prologue's entry relation, weapon-state-expiry
callbacks, DOS preservation of all other state, the diagnostic weapon-age value,
rendering, or a complete tic. Inventory uses the actual
`Inventory.fromPickup (Inventory.toPickup ...)` conversion. Equality with the
original arbitrary `Inventory` is not assumed; canonical reachable inventories
need their own invariant. A weapon timer can reach one here, so the quiet branch
cannot be iterated indefinitely without the action-transition proof.

## Discharge actions now connected to the runtime handler

`Doom/Proofs/WeaponActions.lean` proves the actual production `Weapon.tick` at
pistol windup state 13 and shotgun windup state 21, each with one tic remaining.
For all context values, it establishes the complete returned context, including
pose 155, the selected ammo debit, unchanged other ammo slots, a fresh singleton
firing-event queue, and the flash countdown in the same tic (pistol 7 to 6;
shotgun 4 to 3). Signed arithmetic includes wraparound; positive-ammo spending
also reuses the existing `discharge_spends_one` theorem.

The production state-entry body is now `Weapon.enterWith`, with its recursive
transfers passed as parameters. The live entry point executes this same body;
the recursive interpreter also uses it. `terminal_entry` proves that both firing
actions return the stated result for **any** supplied continuations. Their result
therefore does not rely on an assumed behavior of an opaque recursive function.
There is no fuel cap or duplicated firing implementation. Other recursive paths
remain outside this theorem. The refactor's preservation of the previous
executable is regression-tested, not universally proved for every recursive path.

`Doom/Proofs/E1M1WeaponDischarge.lean` connects the produced singleton event to the
actual `Simulation.weaponTick` event loop, including its early-error handling.
It proves that the firing sample is installed before calling `Simulation.fireGun`,
with pistol accuracy determined by refire and shotgun spread always enabled.

These are **production-side** proofs. They remove an opaque-action obstacle to
composition; they do not establish that the original DOS firing callback or the
entire hitscan/damage/audio handler corresponds. They also do not prove all weapon
state transitions or replace the prior conditional original-byte flash theorem.

## Original discharge bytes now meet the production tick

`Doom/Proofs/OriginalWeaponDischarge.lean` adds an original-byte connection for
both discharge callbacks. `live_tick` starts **after the original actor setter
returns**, at `0x2d8ac` (pistol) or `0x2d92d` (shotgun), and executes twelve real
instructions through the CALL to the flash setter at `0x2d040`. Under its explicit
input relation, the selected ammo word equals the ammo in the actual
`Weapon.tick`, and the original flash-state argument equals that tick's flash
frame. This includes every 32-bit ammo value, including wraparound.

The execution theorem specifies the entire register/memory result without
assuming pointer separation: it re-reads weapon metadata after DEC, just as the
binary does. The production correspondence separately requires valid weapon-table
entries, related ammo, and byte-level separation of the ammo, metadata and CALL
stack word. A memory-frame theorem preserves every word disjoint from both
writes. These are obligations for the eventual reachable-state relation, not
assumed global memory safety.

Additional original-byte segments establish the sound, pose-155 and autoaim CALL
boundaries. They **do not execute or equate those callees**. In particular, this
is not a complete callback theorem, a proof of sound ordering against the Lean
event loop, or a proof that the flash setter has finished installing its state.

The verifier pins both code ranges, their code/data relocations, the state-14 and
state-22 callback pointers and timers, and the relevant weaponinfo entries to the
shareware executable. The interpreter now decodes memory DEC; its register and
memory effect is modeled exactly, while its flags are conservatively forgotten.
No subsequent branch may consume those forgotten flags. These proofs use the
existing flat 32-bit machine model; DOS loading, segmentation, memory faults and
device semantics remain outside this segment’s claim.

Recheck:

```sh
python3 scripts/verify_original_weapon_discharge.py
# With Capstone/Unicorn installed (JIT execution may need sandbox permission):
python3 scripts/verify_original_weapon_discharge.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_weapon_discharge -v
```

The independent x86 check covers 4,096 executions across both guns and four
segments, including unaligned players, wrapping stacks, boundary ammo values,
all registers, complete mapped data memory and ordered writes. It supplements
the universal kernel theorem. Mutated code/table bytes, missing premises,
incorrect timing, debit and flash-slot conclusions are rejected by the proof
checks. The concrete fixtures establish that the representation/separation
premises are satisfiable. The axiom audit admits only the existing standard
Lean axioms.

## Actor and flash setters now execute in the joined path

`Doom/Proofs/E1M1FlashInstall.lean` specializes the existing psprite driver to the
pistol/shotgun flash installation. It proves the driver succeeds from initial
table words and byte-range separation; evaluator success is a conclusion, not
an input. It executes the setter, the `A_Light1` callback, and the actual RET.
The installed timers are **7 / 4**. The later same-tic flash tick reduces these to
6 / 3 and is outside this interval.

`Doom/Proofs/E1M1DischargeSetters.lean` joins the original pose CALL, the reusable
actor setter and RET, indexed ammo debit, flash CALL, complete flash/light
execution and flash RET. `live_joined` reaches this return within a conservative
116-instruction bound and equates the selected ammo, actor pose/timer/sprite/frame,
flash pointer/timer and extra light to the actual `Weapon.fireAction` result.
`aim_execution` extends the execution to the CALL into `P_BulletSlope`, within
118 instructions. It does not execute autoaim itself.

The input relation now starts **after sound**, before the actor pose CALL:
`0x2d8a0` (pistol) / `0x2d921` (shotgun). The proof transports ammo and weapon-table
facts across the real actor setter, derives the flash setter inputs from the
original memory and write footprints, then preserves ammo and pose across the
flash/light writes. There is no assumed correct post-callee state or opaque
callee oracle inside this joined interval. Preconditions still require the
correct initial tables, related ammo, and separation of the participating stack,
actor, player and table words. Concrete kernel-checked fixtures satisfy the
**entire** input record for both guns, positive and boundary ammo, an unaligned
player/actor, and a wrapping CALL stack; these are diagnostic states, not a
reachable-state proof for E1M1.

The new verifier pins all five code ranges (both callbacks, actor setter, psprite
setter, light callback), the actor pose row, flash rows and weapon metadata to the
same executable hash. Its kernel certificate and transitive axiom audit allow
only the existing standard Lean axioms. The optional independent emulator check
executes the entire joined interval to autoaim entry in 1,024 cases, without
stubbing callees. It compares all eight registers, complete mapped data memory,
and all sixteen ordered writes, including the four CALLs and their stack
scratch space. Each case executes 76 instructions. Native arithmetic flags are
not compared; the formal model conservatively forgets unsupported flags.
This is additional diagnostic evidence, not an exhaustive proof by testing.

Six new regression tests pass, along with the six preceding discharge tests.
They reject changed instruction/table bytes, missing representation or memory
preservation premises, incorrect theorem bounds/entry points/outputs, and the
wrong post-install timer. The fixtures instantiate the joined theorem itself.

```sh
./scripts/lake build Doom.Proofs.E1M1DischargeSetters
python3 scripts/verify_e1m1_discharge_setters.py
# With Capstone/Unicorn installed:
python3 scripts/verify_e1m1_discharge_setters.py --cross-check
PYTHONPATH=tests python3 -m unittest test_e1m1_discharge_setters test_original_weapon_discharge -v
```

## Original autoaim controller and the first geometry call

`Doom/Proofs/OriginalBulletSlope.lean` pins all 99 bytes of the original
`P_BulletSlope` at `0x2d7c0..0x2d823`. Universal instruction proofs cover its saved
registers, first geometry CALL, both target-presence branches, both retry CALLs,
all three slope stores, and the real epilogue/RET. Register and memory summaries
retain aliasing effects; an explicit separation premise is required to identify
the angle read after the prologue with the initial actor angle.

`Doom/Proofs/BulletAim.lean` proves the **unchanged production**
`Scene.bulletAim` is the short-circuiting center / +1/64 turn / -1/64 turn sequence
at 1024 units, including error propagation. It proves selection leaves the facing
angle unchanged. `E1M1BulletAim.retry_angles` checks the DOS retry arithmetic for
all 32-bit angles, including wraparound: the final retry subtracts 1/32 turn from
the first retry's angle.

`Doom/Proofs/E1M1BulletAim.lean` extends the previous post-sound firing prefix to
the **first actual CALL into `P_AimLineAttack` (`0x2bb80`)**, with a conservative
127-instruction bound. A request theorem identifies shooter, angle and range
under the explicit angle/memory relation. The previous full input fixtures for
both guns instantiate this extended execution; no new oracle is used before
that first geometry CALL.

After a geometry query returns, the proved continuation either accepts the
slope and executes RET, or makes the next query. Production correspondence
lemmas connect those returned slopes to `Scene.bulletAim` **conditional on** the
query returning the same target presence and slope as Lean. These are interfaces
for the upcoming geometry proof, not a proof that the queries already agree.
The blocks have not yet been composed into a complete autoaim execution with
verified geometry callees. Saved-state preservation by those callees remains
part of that composition.

Two distinctions are explicit: a zero slope can be a successful target, and
`P_BulletSlope` copies the third query's slope even when no target was found.
The all-miss correspondence therefore needs the geometry query to return zero;
it cannot infer that merely from the controller. The Lean selection proof
checks that premise rather than silently assuming it.

The verifier re-extracts the pinned code bytes, file mapping and five data
relocations, then checks the kernel certificate and standard-axiom audit.
Its optional native check runs 1,024 controller cases across all four outcomes,
with wrapping angles/stacks, unaligned actors, zero-slope hits and nonzero-slope
misses. It compares ordered query arguments, all registers, mapped data memory,
writes and the real RET. **Geometry replies are synthetic in this diagnostic**;
it does not execute `P_AimLineAttack` or establish map/traversal parity.
Seven new regression tests and the six preceding discharge-setter tests pass.
They cover modified bytes, missing query/presence/zero-on-miss premises, incorrect
entry points and bounds, concrete controller edges, and the extended firing
fixture. No production engine code changed.

```sh
./scripts/lake build Doom.Proofs.E1M1BulletAim
python3 scripts/verify_original_bullet_slope.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_bullet_slope.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_bullet_slope -v
```

## Original aim ray arithmetic and return

`Doom/Proofs/OriginalAimQuery.lean` pins two segments of `P_AimLineAttack`:
32 bytes at `0x2bb80..0x2bba0` and 26 bytes at `0x2bbff..0x2bc19`.
The first executes four register saves, the angle/range shifts, sine/cosine
reads, and both low-32-bit signed multiplications in 11 instructions. The
reusable decoder now supports register and memory forms of two-operand IMUL;
it conservatively invalidates flags rather than allowing unsupported flag use.

`live_endpoint` proves those displacements produce the exact coordinates used
by the live attack trace. This is whole-map-unit range multiplication: arithmetic
right shift by 16 **before** multiplication, not `FixedMul`. The theorem covers
all 32-bit ranges and angles, including truncation and modular overflow. Actual
attacks separately require a positive range. It reuses `ThrustTables`, with
explicit separation of the three selected table reads from the four stack saves.
Table initialization and DOS loading remain external obligations. A small
production refactor exposes `SolidThing.attackEndpoint`; the kernel checks
`Scene.attackPath_original` by definitional equality with the preceding body.

The second segment executes the actual query epilogue in eight instructions.
It returns zero when `linetarget` is null, otherwise reads `aimslope`, restores
EBP/EDI/ESI/ECX, and executes RET. Its generic summary allows arbitrary memory
aliasing; the caller must establish the return frame and target/slope relation.
A target with slope zero still follows the hit branch.

`Doom/Proofs/E1M1AimQuery.lean` joins the ray segment to the earlier post-sound
firing prefix, now bounded by 138 instructions and stopping at `0x2bba0`.
Separately, `return_to_accept`, `return_to_retry`, and `return_to_last` join the
query epilogue to each controller continuation, under the explicit saved return
address. `last_miss_zero` closes the DOS side of the final-query zero-on-miss
obligation. No traversal result is supplied by an oracle in the firing prefix;
**the middle of the query is still unproved**, including callback setup, origin
addition, shoot height, slope-window initialization and `P_PathTraverse`.

The verifier checks executable hash, segment bytes, file mapping, four data
relocations and the standard-axiom audit. It reuses the empirical comparison of
all 10,240 extracted sine entries with compiled Lean tables. Independent native
checks execute 8,192 ray cases (every fine-angle index) and 1,024 return cases,
including signed/fractional ranges and unaligned/wrapping stacks. They compare
registers, all mapped data memory, write order and instruction counts. Flags are
not compared. These are two real segments, **not** a full geometry execution.

Validation: the configured proof-target build plus the engine/probe targets passed
(408 Lake jobs); all 19 aim/controller/discharge regression tests, nine live
hitscan regressions and 98 internal engine checks passed. The new proof tests
reject changed bytes, incorrect execution contracts, missing correspondence
premises and incorrect return addresses. They also cover all 64 register IMUL
encodings, truncated memory operands, and concrete wrapping return frames.

```sh
./scripts/lake build Doom.Proofs.E1M1AimQuery
python3 scripts/verify_original_aim_query.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_aim_query.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_aim_query -v
```

## Original aim setup through the traversal call

`Doom/Proofs/OriginalAimSetup.lean` pins the 95 original bytes at
`0x2bba0..0x2bbff`. Its 25-instruction execution theorem includes the actual
CALL to `P_PathTraverse` (`0x2c8a0`). The memory summary retains all nine stores
in their original order, including the callback, flags and return-address stack
slots. Actor coordinates are reloaded after global writes, just as in the DOS
instructions; overlapping memory is represented rather than silently ruled out.
A generic frame lemma identifies memory preserved by the setup.

Under explicit shooter/range/displacement representation and separation,
`ready` proves the traversal interface matches the live Lean inputs:

- The shooter's original x/y and the existing `attackEndpoint` coordinates.
- `shootHeight = z + (height >>> 1) + 8` with signed shift and 32-bit wrapping,
  including negative odd heights (the diagnostic states need not be reachable).
- Original shooter and range globals, null `linetarget`, and initial slopes
  `-40960` / `40960` used by `Scene.aimLineAttack`.
- Traversal flags `3`, callback `0x2b760`, saved return address `0x2bbff`, and
  entry PC `0x2c8a0`.

The small production refactor exposes the existing shoot-height function and
names the two initial bounds. Their bodies are unchanged; the kernel checks
`shootHeight_original` definitionally. The shared x86 model adds immediate PUSH
(`68` and sign-extended `6a`), using the existing wrapping byte-memory stack and
preserving flags. The extractor checks the callback's **code-object relocation**
as well as six data-object relocations. Loader correctness remains external;
formal code pointers are code-relative offsets in the established code model.

`Doom/Proofs/E1M1AimSetup.lean` joins these instructions to the firing prefix:
`first_traversal_execution` now reaches traversal entry within **163** modeled
instructions after the preceding sound call. `query_setup_execution` separately
covers all **36** instructions from `P_AimLineAttack` entry to the traversal CALL,
so the same result applies to all three autoaim probes. `inputs_from_ray` reuses
the previous ray-arithmetic proof to discharge displacement correspondence.
`first_traversal_correspondence` combines execution and `Ready` for the same
produced state. Shooter encoding and separation at the setup boundary remain
explicit caller obligations. The existing return/controller proofs are retained
in this combined program; no traversal result or return-frame preservation is
assumed to have been proved.

The certificate audits the execution, memory, production-interface and joined
proofs using only standard Lean axioms. Independent native checks run 1,024 setup
cases, half with deliberately overlapping actor/global/stack memory. They compare
all registers, all mapped data memory, store order and the real CALL destination,
including signed odd heights, coordinate overflow and wrapping/unaligned stacks.
The native callback pointer is relocated to its emulated code base; the callback
and traversal are not executed. Flags are not compared.

Validation passed: the broader 408-job build, the new 184-job joined-proof build,
26 proof regression tests (including seven new setup tests), nine live hitscan
regressions, and 98 internal engine checks. The new tests reject mutated bytes,
wrong bounds/entry PCs, missing representation or separation premises, and a
misidentified code relocation. Kernel-checked fixtures cover the real discharge
prefix and a separate diagnostic state (not assumed reachable) with negative odd height,
coordinate overflow and a wrapping argument stack.

```sh
./scripts/lake build Doom.Proofs.E1M1AimSetup
python3 scripts/verify_original_aim_setup.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_aim_setup.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_aim_setup test_original_aim_query -v
```

## Original traversal initialization and the live firing ray

`Doom/Proofs/OriginalPathInit.lean` pins the 204 original bytes at
`0x2c8a0..0x2c96c`. The execution theorem covers at most 60 modeled instructions
(58–60 according to the two boundary branches), stopping before the first X-axis
stepping comparison. It covers the prologue, intercept pointer reset, early-out
flag, wrapping `validcount` increment, both one-unit boundary nudges, all four
trace globals, relative coordinates, four signed block indices, and the first
fractional X coordinate. All 15 stores and instruction-time reloads are retained
in order, even for overlapping byte memory. The frame theorem identifies reads
unaffected by those writes.

`ready` connects that executed state to `Collision.pathStart`, now used directly
by `Scene.pathTraverse`. The helper exposes the existing calculation; the
boundary adjustment, signed shifts and wrapping arithmetic are unchanged.
The correspondence requires encoded start/end coordinates and blockmap origins,
plus explicit read/write separation. It does not assume a traversal result.
The DOS `validcount` update is proved as a machine-memory fact; equivalence of
DOS visit stamps to Lean's visited-line array remains a later invariant.

`Doom/Proofs/E1M1PathInit.lean` composes this with the actual traversal CALL and
previous firing prefix. `first_path_execution` reaches `0x2c96c` within **223**
modeled instructions from the post-sound firing boundary. `query_path_execution`
is reusable for all three autoaim probes and reaches the same boundary within
**96** instructions from query entry. `inputs_from_setup` reuses the preceding
coordinate theorem, and `first_aim_path_correspondence` carries the live
`attackEndpoint` into the executed grid initialization. Origin encoding and
stack/global separation remain caller obligations, along with the earlier
firing/setup input relations.

The shared instruction model adds EAX/immediate TEST (`a9`) and INC EBX (`43`).
TEST preserves registers/memory and establishes the consumed branch flags.
INC conservatively invalidates flags; the subsequent TEST establishes fresh
flags before either conditional jump. As elsewhere, these proofs use the flat
byte-memory/register/control-flow model, not a full hardware semantics. Loader,
code-memory interpretation, access faults and the reachable-state invariant
remain external obligations.

Validation: 410-job broader build, 186-job joined-proof build, eight new proof
regressions, 22 neighboring aim/query/hitscan regressions, and 98 engine checks.
The tests reject changed bytes, bounds, entry PCs, missing encoding/separation,
and incorrect relocations. Kernel-checked fixtures cover every boundary-branch
combination, negative block coordinates, a wrapping stack, and `validcount`
overflow. These diagnostic states are not asserted reachable in E1M1.
The independent 1,024-case x86 check covers every branch combination, with half
the cases deliberately aliasing globals/stack. It compares every register,
all mapped data memory, the exact store order, stop PC and instruction count.
The certificate separately checks the binary extraction/relocations and audits
the transitive theorem axioms; only standard Lean axioms are allowed.

```sh
./scripts/lake build Doom.Proofs.E1M1PathInit
python3 scripts/verify_original_path_init.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_path_init.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_path_init test_original_aim_setup test_original_aim_query test_hitscan -v
```

## Original X-axis stepping setup and helper reuse

`Doom/Proofs/OriginalAbs.lean` pins the seven-byte Watcom absolute-value helper
at `0x418d8..0x418df`. Its theorem executes the TEST, signed branch, optional
NEG and real RET for arbitrary input registers and byte memory. The result
wraps at `INT_MIN`, as the original executable does. A separate theorem relates
it to successful `checkedPathAbs` calls; the engine's existing explicit
`INT_MIN` rejection is unchanged. This helper is reusable for Y-axis setup.

`Doom/Proofs/OriginalPathXStep.lean` pins the 103-byte caller range
`0x2c96c..0x2c9d3` and includes the already-proved 65-byte `FixedDiv` routine
in the combined program. All three signed direction cases are covered:

- Moving right installs direction `1` and uses one minus the fractional X position.
- Moving left installs direction `-1` and uses that fractional position directly.
- Staying in one column installs direction `0`, unit portion, and Doom's `256`
  sentinel slope, without calling either helper.

The moving paths execute both actual CALLs, the absolute-value helper, all of
`FixedDiv`, their physical stack writes and RETs, and the final portion
adjustment. The continuous execution bound is **45** modeled instructions;
the native success cases take 43 or 44 (10 for the stationary case). The
post-state is at `0x2c9d3`, before the first Y-intercept multiplication.

`PathStart.xStep` extracts the existing production X-axis calculation without
changing its body, and `Scene.pathTraverse` now calls it. The `live` theorem
proves that the executed direction, portion and slope match a successful result
of this function. Its arithmetic-success premise discharges the machine's IDIV
safety condition using `OriginalDivMemory.safe_of_fixed_success`; the division
answer then reuses `result_matches_fixed`. It does not assume an x86 output
value or a matching traversal outcome. Both ordinary and saturated division
are covered. Faulting machine division and the engine's rejected absolute-value
domain remain outside this successful-path theorem.

`Doom/Proofs/E1M1PathXStep.lean` joins the segment to firing. The prefix now
reaches the X-axis result within **268** modeled instructions from the existing
post-sound boundary. `inputs_from_init` derives every new coordinate, block-index
and fraction-slot premise from the preceding initialization theorem. The joined
production theorem therefore requires no additional coordinate encoding at this
seam and no separate assumed IDIV safety. Earlier firing/initialization encoding,
layout and arithmetic-success obligations remain explicit. Loader, hardware
semantics and the reachable-state invariant are still external obligations.

Validation passed: the 412-job broader build, 193-job joined-proof build, eight
new proof tests, 30 neighboring initialization/aim/hitscan regressions, and 98
engine checks. The new tests audit transitive axioms, reject mutations in all
three byte ranges, unjustified tighter execution budgets, changed entry points,
and missing arithmetic-success/encoding premises. Kernel fixtures cover right,
left, same-column and saturated cases with a wrapping stack, plus the preceding
initialization supplying the new inputs. Fixtures are diagnostic boundary states,
not proofs of reachability from E1M1 initialization.

An independent 1,024-case x86 run compares all registers, all mapped data memory,
ordered writes, instruction count and the final PC, with actual relocated CALL
return addresses. Coverage includes 512 stationary, 256 right and 256 left
cases; the moving cases include 169 saturated and 343 ordinary divisions,
211 negative absolute-value inputs and 42 `INT_MIN` helper inputs. Stacks include
unaligned and wrapping addresses. Flags are not compared. The binary certificate
checks file mappings and absence of relocations for all three ranges, then
checks the execution theorem and standard-only Lean axiom audit.

```sh
./scripts/lake build Doom.Proofs.E1M1PathXStep
python3 scripts/verify_original_path_xstep.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_path_xstep.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_path_xstep test_original_path_init test_original_aim_setup test_original_aim_query test_hitscan -v
```

## First grid crossing joined to firing

`Doom/Proofs/OriginalPathIntercept.lean` pins the next **61 bytes / 19
instructions**, `0x2c9d3..0x2ca10`, from the same original DOS executable. Its
execution theorem covers arbitrary registers, memory and incoming flags. It
includes the actual signed `IMUL`/`SHRD` pair, reusing `multiply_correct`, all
three stack writes, wrapped coordinate subtraction, and the signed comparison
that selects the next axis branch.

`Collision.pathFirstIntercept` is now the shared production expression used
for both first intercepts in `Scene.pathTraverse`; the extraction preserves the
existing shift, multiply and add exactly. `OriginalPathIntercept.live` proves
that the first Y-intercept stored by the DOS instructions equals that live
expression. Its `Ready` conclusion also establishes both coordinate deltas,
the Y fraction, shifted-coordinate and stride slots, both Y block indices,
comparison flags, remaining starting coordinates, stack pointer and next PC.
It does **not** yet execute the Y-axis direction/division branch.

`Doom/Proofs/PathXStepFrame.lean` supplies the missing transport facts across the
preceding X-axis setup, including the real absolute-value and division calls.
It proves preservation of the four remaining coordinate registers, the stack
pointer and reads outside the six potentially overwritten stack words. These
facts include the block-index slots needed by the new calculation and hold
even for unaligned or wrapping addresses. They are used by the joining theorem,
not added as new hypotheses at the seam.

`Doom/Proofs/E1M1PathIntercept.lean` extends the continuous post-sound firing
prefix to **287** modeled instructions. `inputs_from_xstep` derives all new
inputs from the previously encoded initialization plus successful production
X-step arithmetic. `first_intercept_correspondence` joins that execution with
the live first-crossing result and Y-axis operands. The earlier geometry,
layout, arithmetic-success and reachable-state obligations remain; this is
still a partial firing proof, not an unconditional whole-game theorem.

Validation: the 415-job broader build, 196-job joined-proof build, kernel
certificates with standard-only transitive axiom audits, targeted proof
regressions, and all 98 engine checks. Eight kernel fixtures include signed
rounding, multiplication/addition overflow and a wrapping stack. Contract tests
reject altered executable bytes, entry points and instruction counts, swapped
arithmetic operands, clobbered-register/slot preservation claims, and dropped
encoding, separation or arithmetic-success premises.

An independent **1,024-case native x86 cross-check** compares all eight
registers, all mapped data bytes, exact write and instruction order, the final
PC, and equality/signed-order flags from the final comparison. Cases include
436 negative starting coordinates, 453 negative products, 372 wrapped sums,
768 unaligned stacks and 256 wrapping stacks. These tests supplement the
universal block theorem; diagnostic states are not claims of E1M1 reachability.

```sh
./scripts/lake build Doom.Proofs.E1M1PathIntercept
python3 scripts/verify_original_path_intercept.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_path_intercept.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_path_intercept test_original_path_xstep test_original_path_init test_original_aim_setup test_original_aim_query test_hitscan -v
```

## Both axes and first crossings joined through grid-walk entry

`Doom/Proofs/OriginalPathYStep.lean` pins **79 new bytes** at
`0x2ca10..0x2ca5f`. The execution theorem follows all three Y-direction
branches and the actual absolute-value and `FixedDiv` calls/returns, reusing
the existing helper proofs. It explicitly requires the incoming signed
comparison flags produced by the preceding intercept block. Its successful
execution bound is **41** instructions; `live` obtains division safety from
the successful production `PathStart.yStep` result. That helper is now used by
`Scene.pathTraverse`, with the previous calculation preserved exactly.

`Doom/Proofs/OriginalPathSecondIntercept.lean` pins the next **32 bytes / 10
instructions**, `0x2ca5f..0x2ca7f`. Reusing the existing signed multiplication
proof, it connects the second crossing to `Collision.pathFirstIntercept` and
establishes the X stride slot, initial map-cell indices, zero loop counter,
stack pointer and grid-walk entry PC. The accompanying memory-frame proofs
show that the first crossing, first stride and prior direction survive both
the Y-axis helper calls and this second crossing calculation.

`Doom/Proofs/E1M1PathGridSetup.lean` joins the pieces to the existing post-sound
firing prefix, now bounded by **338** modeled instructions. Its `Ready`
conclusion establishes both first crossings, both directions, both strides,
the starting cell and zero iteration counter at `0x2ca7f`. `blocks_from_init`
and `grid_observation_from_init` transport coordinate and stack facts all the
way from the previously encoded path initialization: no new representation
assumption or matching-output hypothesis is introduced between blocks.
Both successful production axis calculations supply their respective machine
division conditions.

This completes the **numeric setup before grid-cell visitation** in the
current firing connection. It does not prove the cell visitors, ordered
intercept collection, aim callbacks, whole firing action, or whole-game
correspondence. The existing geometry/layout and preceding post-sound firing
obligations remain explicit, as do loader/hardware semantics and reachable-state
invariants. The production rejection of `abs(INT_MIN)` and faulting divisions
is not silently removed.

Validation passed the 310-job broader proof build, 199-job joined-proof build,
191-job runtime build, kernel byte certificates and standard-only transitive
axiom audits, and all 98 engine checks. New contract/fixture regressions cover
up/down/stationary/saturated branches; both crossings through a concretely
encoded initialization with wrapping stack; incoming comparison flags; retained
memory; both arithmetic-success premises; original byte/file mappings; and
changed bounds/entry points. Diagnostic fixtures do not assert reachability.

The independent **1,024-case native x86 cross-check** runs the combined new
setup through `0x2ca7f`, including the real helper calls and returns. It compares
all eight registers, all mapped data memory, ordered writes, instruction counts
and the final PC, with actual entry `CMP` flags. Coverage includes 512 stationary,
256 increasing-Y and 256 decreasing-Y cases; 181 saturated and 331 ordinary
divisions; 213 negative absolute-value inputs including 42 `INT_MIN` machine
helper cases; 251 negative products and 523 wrapped intercept sums. Stacks
include unaligned and wrapping addresses. Final flags are not compared.

```sh
./scripts/lake build Doom.Proofs.E1M1PathGridSetup lean-doom collision-probe fidelity-probe doom-tests
python3 scripts/verify_original_path_ystep.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_path_ystep.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_path_ystep test_original_path_intercept test_original_path_xstep test_original_path_init test_hitscan -v
```

## First cell dispatch and line-iterator bounds joined

`Doom/Proofs/OriginalPathCell.lean` pins **54 bytes** at
`0x2ca7f..0x2cab5`. It proves both flag gates, their actual iterator calls,
coordinate/callback/return-word arguments, and the caller-side return tests.
`first_visit_execution` establishes line-before-thing dispatch;
`after_line_execution` starts at the real line-return PC and proves that a
zero result aborts before the thing gate. These prefixes stop at actual
iterator entries or caller continuations; they do not assume iterator results.

`Doom/Proofs/OriginalLineBounds.lean` pins **33 entry bytes** at
`0x2c520..0x2c541` and **10 return bytes** at `0x2c587..0x2c591`.
It proves the saved-register/callback prologue, all four signed bounds tests,
and the successful early-return epilogue for outside cells, in at most **16**
modeled instructions. Inside cells stop at `0x2c541`, before the first BLOCKMAP
index lookup. The arbitrary-memory execution summary retains stack/global
alias behavior. The separate production correspondence theorem requires
encoded coordinates and dimensions, dimensions below `2^31`, and separation
of dimension globals from the two prologue writes. Under those conditions,
the machine branch equals `Collision.pathCellInside`, the predicate now used
by the live `Scene.pathTraverse`. The production expression is unchanged.

`Doom/Proofs/E1M1PathCell.lean` extends the continuous post-sound firing prefix
to that bounds result, with a bound of **360** instructions. The original aim
caller writes traversal flags `3`; a memory-frame chain carries those flags
through initialization, both axis helper calls and both crossings to the
first line dispatch. No fresh “line flag is enabled” premise is added at the
dispatch point. The theorem also establishes the iterator's actual X/Y
arguments from the earlier production path geometry. The caller's concrete
stack/global separation remains explicit.

This is a proof of first dispatch and the line bounds boundary, not of a
complete cell visit. The line-list loop, valid-count filtering, line callback,
thing iterator/callback, subsequent cells and intercept ordering remain open.
The live bounds theorem's dimension encoding/separation must still be supplied
by the caller's map-memory invariant when connecting the list body. Earlier
geometry, successful arithmetic, sound, loader/hardware and reachable-state
obligations also remain; this is not whole-game equivalence.

Validation includes a 421-job broader proof/runtime build, the 202-job joined
proof build, extracted-byte/file-offset/relocation checks against the pinned
DOS executable, standard-only transitive axiom audits, and all 98 engine
checks. All 33 focused/neighbor regressions pass after correcting and rerunning
one finite-address fixture proof. Kernel fixtures and negative contract tests cover exact upper bounds,
negative coordinates/dimensions, line-before-thing ordering, false-return
aborts, preserved return words, signed dimension encoding, stack separation,
caller-supplied flags, changed bytes and instruction bounds.

The **2,048-case native x86 cross-check** covers all 256 flag bytes for each
gate, both return-site tests, and inside/outside bounds branches. It compares
all eight registers, all mapped data memory, ordered writes, instruction
counts and final PCs, including unaligned and wrapping stacks. Code-object
relocations are normalized by the explicit code base. Final flags are not
compared. An instruction hook enforces each stop PC even when Unicorn reuses
a translated block; no iterator or callback is stubbed.

```sh
./scripts/lake build Doom.Proofs.E1M1PathCell
python3 scripts/verify_original_path_cell.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_path_cell.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_path_cell test_original_path_ystep test_original_path_intercept test_hitscan -v
```

## BLOCKMAP lookup and first line-list item joined

`Doom/Proofs/OriginalLineCell.lean` pins the **70 bytes** at
`0x2c541..0x2c587`. Its eight-instruction lookup proves the row-major cell
calculation, signed 16-bit list-offset load, doubling of the offset and addition
to the BLOCKMAP lump base. `Collision.pathCellIndex` now names the unchanged
index expression used by `Scene.pathTraverse`; `live_index` relates its natural
index to the machine word calculation. `live_lookup` obtains the same list
pointer from explicit table/lump/offset encodings and the accepted offset bound
`off < 32768`. The pointer still addresses the list's leading zero: vanilla
visits linedef 0 rather than skipping that word.

The next instruction proofs cover one list item: sign-extend the short, stop
on exactly `0xffff`, form `lineBase + id*62`, compare the valid-count field at
byte offset 54 with the traversal counter, and either advance by two bytes
without writing memory or stamp the line before its real indirect callback.
`visit_execution` covers those branches in at most **11** instructions;
`first_execution` joins lookup and the item in at most **19**. The callback
return-site test is also proved: zero goes to the existing failure epilogue,
nonzero goes to the list increment. Callback execution itself remains open.

The stamp/CALL summary retains arbitrary alias behavior: the indirect target
is read **after** stamping and **before** pushing the return word `0x2c578`.
`callback_observe` requires explicit separation to conclude that the original
callback pointer and stamp survive; `callback_frame` protects other words.
`skip_observe` establishes the unchanged memory and two-byte advance for the
actual duplicate branch. Relating the DOS valid-count representation to Lean's
`seen` array across the entire traversal remains a list-loop invariant to prove.

The limited x86 model adds `loadSignedHalf` for full memory addressing, needed
by the actual `MOVSX EAX, word [EDX+EAX*2]`. Existing simple MOVSX decodings stay
unchanged. Unsupported register/truncated forms still fail closed. This extends
the explicit instruction-model trust boundary; it is not a complete CPU model.

`Doom/Proofs/E1M1LineCell.lean` extends the continuous post-sound firing prefix
to at most **379** instructions, retaining the previous input premises. Outside
cells have already returned; inside cells now reach the first item's sentinel,
duplicate continuation, or actual indirect callback entry. `bounds_to_lookup`
transports coordinates, width, globals and offset reads from iterator entry
through the prologue and bounds check, using explicit `MapData` encoding and
stack separation. Those encodings must still be established from the original
map image and maintained by the surrounding caller; the theorem does not
assume a matching output at the interior lookup PC.

Validation: the joined 204-job proof build, broader 426-job proof/runtime build,
pinned EXE byte/file-mapping/relocation certificates, standard-only transitive
axiom audit, 98 engine checks and 33 focused/neighbor regressions passed. The
initial axiom audit correctly rejected a compiler-trusted shortcut emitted by
`bv_decide` for the sentinel lemma; replacing it with a direct signed-value
proof passed the focused audit recheck. No new axiom or unfinished proof remains.

The **2,048-case native x86 check** compares all eight registers, mapped data
memory, ordered writes, exact prefix instruction counts and final PCs. It
covers 299 sentinel cases, 748 duplicate skips, 745 fresh-line calls, 299
leading-zero visits, callback return gates, unaligned/wrapping stacks and
stamp/callback/return-word aliases. Negative signed offsets/IDs additionally
exercise the machine summary outside the accepted production profile. Code
pointers use an explicit code-base normalization; final flags are not compared.
The emulator executes the real indirect CALL and stops before callback code;
no callback result is stubbed.

```sh
./scripts/lake build Doom.Proofs.E1M1LineCell
python3 scripts/verify_original_line_cell.py
# With Capstone/Unicorn installed:
python3 scripts/verify_original_line_cell.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_cell test_original_path_cell test_original_path_ystep test_hitscan -v
```

This proves one list item, not the full list loop, full cell, complete shot or
whole-game equivalence. The line-intersection callback, its register/memory
contract, ordered list induction, valid-count/seen relation and thing iterator
are still required. Earlier sound, map initialization, reachability and
loader/hardware obligations remain explicit.

## Line-intercept branch selection and first point-side call

`Doom/Proofs/OriginalLineInterceptEntry.lean` pins the **89 bytes** at
`0x2c5f0..0x2c637` and `0x2c64d..0x2c65f`. Its instruction proof executes the
five register saves, local-stack allocation, four ordered signed comparisons,
coordinate loads and actual first helper CALL, in at most **22** instructions.
The machine summary permits arbitrary memory aliases; loads observe the memory
left by the real stack writes.

The production predicate `Collision.Divline.usesDivlineTest` is extracted from
the existing `lineIntercept` condition without changing behavior. A component
strictly outside ±1048576 raw units (±16 map units) chooses the divline test;
equality stays on the linedef-test path. `selection_live` proves that this
production choice matches the original branches under explicit memory encoding
and stack-separation premises.

`live` connects that choice to the first point coordinates, data pointer,
saved line pointer, stack pointer, pushed return word and actual helper PC.
Wide traces send the wall's first vertex to `P_PointOnDivlineSide` (`0x2c1e0`);
short traces send the trace start to `P_PointOnLineSide` (`0x2c010`). The
`first_frame` theorem preserves any data word separate from the five saves
and final return-word write. This is a reusable memory contract for the helper
bodies; their geometry and returned side are not yet proved.

`Doom/Proofs/E1M1LineInterceptEntry.lean` joins this prefix to the prior firing
chain, with a **401-instruction upper bound**. It continues only if the prior
prefix actually reaches the line callback. Outside cells, sentinels and
skipped-duplicate boundaries remain unchanged. `callback_live` explicitly
requires arrival at that callback and its input representation; the firing
join does not silently establish those memory encodings or full list traversal.

Validation: the 206-job joined proof build, broader 320-job proof build,
191-job runtime build, pinned EXE
byte/file-mapping/relocation certificates, standard-only transitive axiom audit,
32 focused/neighbor regressions and all 98 engine checks passed. There are no
new axioms or unfinished proofs in these modules.

The native check covers **2,048 cases**, comparing all eight registers, all
mapped data memory, ordered writes, exact instruction counts and final PCs.
It includes all five branch paths, 332 exact-boundary cases, 341 cases whose
stack writes alias trace globals, and 1,023 wrapping-stack cases. It stops at
the real helper entry, with no stubbed result. Code and return pointers use an
explicit code-base normalization; final flags are not compared.

```sh
./scripts/lake build Doom.Proofs.E1M1LineInterceptEntry
python3 scripts/verify_original_line_intercept_entry.py
# With pinned Capstone/Unicorn dependencies installed:
.tools/x86-check/bin/python scripts/verify_original_line_intercept_entry.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_intercept_entry test_original_line_cell test_original_path_cell test_hitscan -v
```

## Complete linedef point-side helper and caller return

`Doom/Proofs/OriginalLineSide.lean` pins all **163 bytes** of
`P_PointOnLineSide`, at `0x2c010..0x2c0b3`. The instruction proof covers all
vertical, horizontal and diagonal paths through the real RET, in at most
**34 instructions**. It retains the original signed endpoint comparisons,
arithmetic right shifts by 16, wrapping subtraction, inlined fixed-point
multiplication and final signed comparison. A diagonal tie returns side 1;
axis equality follows its own original branch. Zero-length lines are included.
The multiplication steps reuse `BlockSummary.multiply_correct` and the
existing original fixed-multiply theorem.

`live` proves that the returned EAX is exactly 0 or 1 as selected by the
production `Collision.Line.pointSide`, given the original line/vertex encoding,
point registers and explicit stack separation. No coordinate-magnitude bound
is imposed. `returned` proves restoration of ECX, ESI, EDI and EBP, the stack
adjustment and actual return address. `frame` preserves words outside the four
saved-register slots. The unconditioned machine execution summary allows stack
aliases; the production interpretation requires the stated separation.

`Doom/Proofs/E1M1LineSide.lean` carries line fields from the enclosing line
callback into the helper with `entry_inputs`. Its `LineData` premise explicitly
protects those fields from both the callback's writes and the helper's saves.
`short_result` then proves both the live side result and return to `0x2c65f`.
The continuous post-sound firing prefix extends to at most **435 instructions**
on actual linedef-helper entry. The divline branch and earlier stopping
boundaries remain unchanged; this is not yet a complete autoaim query.

The limited instruction model adds register-form `SETG`, preserving flags and
unrelated register bits, and fails closed for its unsupported memory form or
missing flags. The native check exercises all eight byte-register encodings
and all eight SF/ZF/OF combinations (**64 cases**). This is an explicit extension
to the model's instruction coverage, not a verification of the full CPU.

Validation: the 208-job joined proof build, broader 322-job proof build,
191-job runtime build, pinned EXE
byte/file-mapping/relocation certificates, standard-only transitive axiom audit,
40 focused/neighbor regressions and all 98 engine checks passed. The new
modules contain no unfinished proofs or additional axioms.

The complete-helper native check covers **2,048 cases**, comparing all eight
registers, all mapped data memory, ordered writes, exact instruction counts and
the final PC. Coverage includes 303 zero-length lines, 109 diagonal product
ties, 341 stack aliases and 1,023 wrapping-stack cases. It executes the real
helper through RET without stubs. Return code pointers use the explicit code
base normalization; helper final flags are not compared (isolated SETG flags
are checked).

```sh
./scripts/lake build Doom.Proofs.E1M1LineSide
python3 scripts/verify_original_line_side.py
.tools/x86-check/bin/python scripts/verify_original_line_side.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_side test_original_line_intercept_entry test_original_line_cell test_original_path_cell test_hitscan -v
```

## Complete divline point-side helper and caller return

`Doom/Proofs/OriginalDivlineSide.lean` pins all **199 bytes** of
`P_PointOnDivlineSide`, at `0x2c1e0..0x2c2a7`, and proves every branch through
the real RET in at most **44 instructions**. This includes the axis cases,
the sign-bit shortcut, wrapping coordinate subtraction, arithmetic shifts by
8, both fixed-point multiplications, and the final signed comparison. The
shortcut runs before multiplication: even when the shifted products would
tie, their sign bits can select side 0. The proof preserves this behavior.

`live` equates returned EAX with production `Collision.Divline.pointSide` for
all encoded input coordinates, under explicit stack/data separation. There
is no coordinate-magnitude restriction. `returned` restores ECX, ESI, EDI and
EBP, proves the stack adjustment and reads the actual return address;
`frame` preserves words outside the four saved-register slots. The machine
execution theorem itself includes overlapping data and stack addresses.
The fixed-multiply summaries, memory-separation lemmas and prefix composition
are reused. The sign-mask lemma is proved with bit-vector algebra in Lean.

`Doom/Proofs/E1M1DivlineSide.lean` transports the trace globals and point
registers from the actual line-intercept callback. `wide_result` proves the
production side result and return to **0x2c637**. The previously proved short
branch still returns to **0x2c65f**. The composed post-sound firing prefix now
has a conservative bound of **479 instructions**, continuing the divline
helper only at its actual entry PC. This does not yet complete the second
endpoint, intersection calculation or autoaim query.

The instruction model adds memory-source XOR (`33 /r`, memory forms only)
and register-immediate TEST (`F7 /0`, register forms only). The latter reuses
the existing TEST semantics. Address evaluation uses the old register state,
even when the XOR destination is also the address base. Unsupported forms and
truncated encodings fail closed. Two older proofs (death-state choice and weapon raising) need larger local
simplifier step budgets after extending the instruction datatype; their
statements and executable behavior are unchanged.

Validation: the 210-job joined proof build, broader 324-job proof build,
pinned EXE byte/file-mapping/
relocation certificate, standard-only transitive axiom audit (30 declarations),
48 focused/neighbor regressions, 191-job runtime build and all 98 engine checks
passed. Neither new proof module introduces axioms or unfinished proofs.

The native check covers **2,048 complete-helper cases** with all eight
registers, mapped data memory, ordered writes, exact instruction counts and
final PC checked. It includes 339 sign-shortcut cases, 47 multiplication ties,
303 zero-length lines, 341 stack aliases and 1,023 wrapping-stack cases.
Another **256 instruction cases** check XOR/TEST across all eight registers,
including destination/address aliasing, and compare their defined ZF/SF/OF/CF
flags. Helper final flags and undefined CPU flags are not compared; code
return addresses use the explicit code-base normalization. No helper stubs
are used. These tests supplement the proof and do not replace it.

```sh
./scripts/lake build Doom.Proofs.E1M1DivlineSide
python3 scripts/verify_original_divline_side.py
.tools/x86-check/bin/python scripts/verify_original_divline_side.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_divline_side test_original_line_side test_original_line_intercept_entry test_original_line_cell test_original_path_cell test_hitscan -v
```

## Second endpoint tests and same-side rejection

`Doom/Proofs/OriginalLineSecondPoint.lean` pins **81 additional bytes** from
`PIT_AddLineIntercepts`: `0x2c637..0x2c64d`, `0x2c65f..0x2c691`, and
`0x2c711..0x2c71a`. It executes both real second-point calls using the complete,
previously proved helpers. Long traces load the wall's second vertex; short
traces add the trace components with 32-bit wrapping. ESI retains the first
side result across the second helper. Both branches meet at `0x2c683`.

The byte-level summary covers the second call and shared decision in at most
**62 instructions**. Equal side results execute the real callback epilogue
and RET with EAX=1; unequal results stop at **0x2c691**, immediately before the
intersection-fraction setup. `same_side_none` proves that the production
`Collision.lineIntercept` returns `.ok none` for the equal-side branch. That
existing function is now public so the correspondence theorem can reference
it; its implementation and gameplay behavior are unchanged. No fraction
calculation or intercept-list insertion has been assumed or stubbed.

The memory frame preserves words outside the five second-call save/return
slots. Thus the same-side return leaves the intercept pointer and array
unchanged when separated from the stack. Native fixtures additionally check
the restored caller registers, stack adjustment, and actual return address.

`Doom/Proofs/E1M1LineSecondPoint.lean` composes the new segment into the
post-sound firing prefix, now conservatively bounded by **541 instructions**.
`entry_inputs` transports the encoded line, trace and endpoints from the
original enclosing callback, through the first helper, into the second test.
It obtains the first side result from the existing proof. `callback_rejection`
connects that chain to the production no-intercept result and to the original
callback return address. The input contract explicitly requires the second
vertex to encode the wrapping sum of the first vertex and line delta, and
protects the data against both helpers' reused stack slots. Deriving this
contract from the original loaded map remains separate work.

Validation: the 212-job joined proof build, broader 326-job proof build,
191-job runtime build, pinned EXE byte/file-mapping/relocation certificates,
standard-only transitive axiom audit (41 declarations), 41 focused/neighbor
regression checks and all 98 engine checks passed. Two test-harness issues
were corrected and rechecked individually. No new axioms or unfinished proofs
were introduced.

The native check runs **2,048 cases** through the complete second helper and
same-side decision: 501 wide rejects, 523 wide continuations, 515 short rejects,
and 509 short continuations. It checks all eight registers, mapped data memory,
ordered writes, instruction counts and final PCs. Coverage includes 393
sign-shortcut cases, 429 wrapping endpoint sums, 340 stack aliases and 1,024
wrapping stacks. These runs start at the first-helper return with first side
0 or 1; the kernel proof separately supplies that value from the enclosing
callback. Native checks do not compare final flags, and code return addresses
use the explicit code-base normalization. The verifier validates both helper
byte sequences as well as the 81 new bytes against the pinned EXE.

```sh
./scripts/lake build Doom.Proofs.E1M1LineSecondPoint
python3 scripts/verify_original_line_second_point.py
.tools/x86-check/bin/python scripts/verify_original_line_second_point.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_second_point test_original_divline_side test_original_line_side test_original_line_intercept_entry test_hitscan -v
```

## Crossing-line intersection fraction

`OriginalInterceptVector` pins all 100 bytes of `P_InterceptVector`
(`0x2c2d0..0x2c334`) and proves the complete call/return path, including its
original 65-byte `FixedDiv` callee. Under encoded input divlines, separation
from the five register-save words, and successful production arithmetic, its
returned EAX equals the raw fixed-point result of the live
`Collision.interceptVector`. This includes a zero denominator, signed
arithmetic shifts by eight, the two inlined fixed multiplications per
numerator/denominator, wrapping subtraction/addition, division truncation and
saturation. The IDIV success condition is derived from the production
function's success; it is not silently inferred from a nonzero denominator.
The helper restores EBX, ECX, ESI, EDI, EBP and its actual stack return address.
Its frame theorem protects every word separated from the nine possible stack
writes, including the division callee’s saves.

The denominator's `SUB EDI,EAX; JNE` needs subtraction flags. The instruction
model now provides an opt-in byte decoder that retains register SUB's
ZF/SF/OF/CF. It refines the previous flag-forgetting interpretation without
changing register, memory or PC effects (`sub_flags_core`). Selection depends
on decoded operations, not PCs or expected answers. Earlier ranges continue
to use their conservative decoder; the new helper uses the refined decoder.
This remains the project's limited x86 model, not a verified full emulator.

`OriginalLineFraction` pins the 42-byte callback setup
(`0x2c691..0x2c6bb`), derives the local divline from actual vertex/line loads,
and proves execution through the helper's return to `0x2c6bb` in at most
80 instructions. Its source-data relation explicitly protects the source
reads from the local writes, call word and helper saves; it supports unaligned
addresses and wrapping stacks. `E1M1LineFraction` appends this to the existing
post-sound pistol/shotgun path, with a bound of 621 instructions. The successful
arithmetic condition is needed only when the path reaches the fraction call.
The map encoding/separation facts at that callback boundary still need to be
supplied by the enclosing traversal invariant. This is not a complete firing
or whole-game correspondence theorem.

The extracted-byte verifier checks the pinned EXE hash, file mapping and
relocations for the helper, setup and original division code. It audits the
transitive kernel theorem axioms. Its native check runs 2,048 cases, comparing
all eight registers, mapped byte memory, ordered writes, instruction counts,
final PCs and the subtraction flags used by JNE. Coverage includes 235 zero-denominator returns, 1,343 ordinary divisions,
235 saturations, 235 hardware divide errors, 168 stack aliases and 1,008
wrapping stacks. Hardware fault cases supplement testing; the universal execution/live
proof currently covers successful production results. Return code addresses
use explicit code-base normalization. Other final flags are not compared.

```sh
./scripts/lake build Doom.Proofs.E1M1LineFraction
python3 scripts/verify_original_intercept_vector.py
.tools/x86-check/bin/python scripts/verify_original_intercept_vector.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_intercept_vector test_original_line_second_point test_original_divline_side test_original_line_side test_hitscan -v
```

## Original line callback through rejection, insertion and return

`OriginalLineFinish` pins the 95 bytes at `0x2c6bb..0x2c71a` and proves
execution of every suffix branch through its actual RET in at most 23
instructions. A negative signed fraction returns success without inserting;
a nonnegative fraction stops traversal only when early-out is enabled, the
fraction is strictly below 65536, and the line's backsector pointer is null.
All other cases append the fraction, line marker and line pointer and advance
the global cursor by twelve bytes. The proof retains the actual store order
and all byte-memory effects, including aliasing. Its return-PC theorem makes
separation of the caller's return word explicit.

The live bridge relates this decision to `Collision.lineIntercept` and the
production early-out condition. `append_encoded` proves that a represented
array of intercepts becomes the same array with the new line appended: every
earlier record stays in place, including equal-distance entries. It requires
the original cursor to point at the array end and explicit separation of the
old records, new record and cursor global. `append_live` connects the actual
production append operation under its existing limit of fewer than 128
entries. Overflow behavior is not claimed. `appendIntercept` is now public
for this proof; its runtime body is unchanged.

`E1M1LineFinish` joins the suffix to the existing post-sound pistol/shotgun
prefix with a 644-instruction upper bound. `fraction_inputs` derives the
fraction and restored line pointer from the preceding proved helper; the
backsector and early-out global representations at that boundary are still
explicit premises. No new arithmetic precondition is added beyond the
preceding successful-fraction condition. This is a callback-prefix result,
not the completed list iterator or full firing action.

The verifier checks the pinned EXE hash, mapped bytes and relocations, and
strictly audits 28 declarations for transitive axioms. Eight regression tests
reject modified bytes, weakened input/separation/capacity contracts, incorrect
thresholds, and changed execution bounds. Concrete fixtures include unaligned
records, wrapping addresses/stacks, intentional cursor and saved-register
aliases, the 127-to-128 capacity boundary, and two equal-distance records ahead
of a third. The independent x86 run passes 2,048 cases, comparing all eight
registers, mapped byte memory, ordered writes, instruction counts and actual
return PCs. It covers 512 negative returns, 1,320 insertions and 216 early
stops, including 228 wrapping buffers and 636 cursor/stack aliases. Final
flags are not compared. These native samples supplement the kernel proofs;
they are not exhaustive E1M1 executions.

```sh
./scripts/lake build Doom.Proofs.E1M1LineFinish
python3 scripts/verify_original_line_finish.py
.tools/x86-check/bin/python scripts/verify_original_line_finish.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_finish test_original_intercept_vector test_original_line_second_point test_original_divline_side test_original_line_side test_hitscan -v
```

## Original callback return and repeated duplicate skips

`OriginalLineResume` reuses the pinned iterator and epilogue bytes. It proves
that the real callback return at `0x2c578` either advances the restored list
cursor by exactly two bytes and reaches the next list header, or returns zero
through the iterator's own epilogue. The latter restores EDI from its saved
word, consumes the iterator's frame, and reads its actual return address.
No callback stub or assumed return jump is used. The continuation takes at
most five instructions. `finish_continue` derives the returned cursor from
the callback's actual saved word and requires both it and the callback return
word to be separated from intercept writes.

For repeated duplicates, `duplicates_from_memory` derives all successive
iteration conditions from one initial memory window: each non-sentinel signed
short addresses a linedef stamped with the current valid count. `skip_execution`
then proves any finite run of these entries, with at most ten instructions per
entry. `skip_observe` and `next_item` prove unchanged byte memory and exact
cursor advancement, so the caller does not have to supply the same facts anew
at each iteration. A following `0xffff` terminator takes seven instructions
through the success return. `sentinel_observe` proves the resulting success
value, unchanged memory, restored EDI, stack pointer and actual parent return
address. Signed-short addressing and modular 32-bit pointer arithmetic remain
part of the model.

`E1M1LineResume` joins the post-callback continuation to the firing prefix with
a 649-instruction bound. `line_list_return_execution` further joins an arbitrary
finite already-visited suffix and terminator, with a bound of `656 + 10*count`.
Its window and terminator premises are explicit facts at the resumed header;
this does not yet derive all list/map invariants from E1M1 startup or handle a
fresh callback during the repeated suffix.

The verifier rechecks all four reused byte ranges and audits 28 declarations.
Eight focused tests reject changed bytes, missing memory-window/return-frame
conditions, a wrong sentinel or cursor stride, and changed execution bounds.
A concrete three-entry window includes a leading zero, a repeated line, and a
list that crosses address zero. Independent x86 checks pass 2,048 cases: 1,024
execute the original callback suffix through its return and caller resumption
(928 continue, 96 stop), and 1,024 execute duplicate-list runs through the
sentinel and actual iterator RET. They compare all eight registers, mapped
byte memory, ordered writes, instruction counts and PCs, with no helper stubs.
Wrapping stacks/lists, saved-frame aliases and signed-short edge cases are
diagnostic inputs, not claims about reachable E1M1 states. Final flags are not
compared.

```sh
./scripts/lake build Doom.Proofs.E1M1LineResume
python3 scripts/verify_original_line_resume.py
.tools/x86-check/bin/python scripts/verify_original_line_resume.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_resume test_original_line_finish test_original_line_cell test_original_path_cell test_hitscan -v
```

## Crossing-line tail with pre-helper memory invariants

`OriginalLineTail` now composes fraction setup at `0x2c691`, the complete
intersection helper and `FixedDiv`, callback rejection/early-out/insertion,
and actual callback return into the line iterator. Its execution bound is
108 instructions. This starts after the crossing tests; it does not yet derive
all inputs from callback entry.

Three connected results remove post-helper assumptions:

- `fraction_frame` and `frame` preserve protected memory through scratch writes
  and optional intercept insertion. `finish_inputs` derives the live early-out
  and backsector conditions from the original pre-helper memory. The saved list
  cursor and return word are likewise preserved from that boundary.
- `live_append` joins production `Collision.appendIntercept`, the ordered DOS
  record representation, and the cursor increment. It requires initial array
  encoding, capacity below 128, successful fraction arithmetic, and explicit
  separation of old records, new records, globals, and stack scratch.
- `preserves_seen` transports the list IDs, line-table base, epoch and visited
  stamps. `through_sentinel` then composes a crossing tail with any finite suffix
  of already-visited entries and the actual sentinel return, bounded by
  `115 + 10 * count` instructions. `E1M1LineTail` joins this to the post-sound
  firing prefix, bounded by `656 + 10 * count`. Its geometry, memory and list
  contracts are still supplied at the crossing boundary.

The extraction manifest checks seven pinned byte ranges against the original
shareware executable and verifies their relocations. The axiom audit covers
all new public theorems and the byte certificates. Concrete kernel fixtures
exercise a nonempty duplicate suffix after insertion. Native checks run 2,048
cases through original setup/helper/division/callback/iterator instructions,
without helper stubs, comparing all registers, mapped byte memory, ordered
writes, instruction count and final PC. Coverage includes negative fractions,
parallel lines, early stops, insertion, duplicate suffixes and wrapping stack
or record addresses. These samples supplement the conditional universal proofs;
they are not a whole-game theorem. Final native flags are not compared.

```sh
./scripts/lake build Doom.Proofs.E1M1LineTail
.tools/x86-check/bin/python scripts/verify_original_line_tail.py --cross-check
PYTHONPATH=tests python3 -m unittest test_original_line_tail test_original_line_resume test_original_line_finish test_original_intercept_vector -v
```

## Crossing callback from entry through iterator resumption

`OriginalLineCrossing` moves the crossing-tail contract back to callback entry
at `0x2c5f0`. It reuses the existing prologue, first-side and second-side proofs
for both short-trace and wide-trace branches. Initial geometry and unequal
production side results imply arrival at `0x2c691`; this is now derived rather
than separately assumed at the fraction boundary.

`tested_frame` carries protected words through both side calls, and
`fraction_inputs`/`tail_inputs` derive the fraction-helper geometry and
flag/backsector facts from entry memory. `saved_cursor` proves that the
prologue saves the incoming EDX in the correct stack slot and that both side
calls preserve it. `continued` combines this with the existing tail proof to
restore that cursor, advance by two bytes, and return with ESP increased by
four bytes relative to callback entry. Return addresses are read from the
original frame, with separation from optional record writes explicit.

`live_append` now relates production append, ordered DOS records and cursor
advance using array encoding and protection at callback entry. `frame` also
preserves protected words through the complete crossing callback. Both results
still require explicit geometry, memory separation, successful arithmetic and,
for append, capacity below 128. No new post-side-test encoding assumptions are
introduced. These requirements must eventually be maintained by the enclosing
line-list loop and supplied from reachable map state.

`execution` composes the actual instructions from callback entry through
iterator resumption with a conservative 270-instruction bound.
`E1M1LineCrossing.callback_execution` connects that execution to the existing
post-sound firing prefix, bounded by 649 instructions. It remains conditional
on reaching a crossing line with the entry contract; it does not claim that
every shot crosses a line or establish complete mixed-list iteration.

The extraction manifest checks fourteen pinned original byte ranges. The
strict axiom audit covers their certificates and all new public theorems.
Concrete kernel fixtures establish satisfiable entry contracts for both
trace-size branches and check the appended fractions, cursor and restored
stack. Mutation tests reject altered bytes and missing entry/separation/capacity
conditions. This batch adds proof composition, not new instruction semantics;
no new native sampling is claimed.

```sh
./scripts/lake build Doom.Proofs.E1M1LineCrossing
python3 scripts/verify_original_line_crossing.py
PYTHONPATH=tests python3 -m unittest test_original_line_crossing test_original_line_tail test_original_line_second_point test_original_line_intercept_entry -v
```

## Fresh dispatch and conditional mixed iteration

`OriginalLineDispatch` starts at the list header (`0x2c57f`) and proves the
fresh-line path through the valid-count stamp, indirect callback CALL, both
crossing tests, fraction arithmetic, optional insertion and iterator resumption.
The composed bound is 281 instructions. Its `view` uses the callback ABI
registers with the original pre-dispatch memory; it does not assume memory
facts after the stamp or CALL. `crossing_inputs` and `tail_inputs` transport
that initial geometry/global data across the two writes. The return word
`0x2c578` is generated by the CALL, rather than required in initial memory.
Explicit separation protects the indirect target, geometry and stamp.

`continued` proves that one continuing fresh callback advances the short-list
cursor by two bytes and restores the iterator stack pointer. `frame` preserves
protected initial words. `marked_seen` proves that the newly written valid-count
stamp survives the callback and its optional insertion, while the epoch,
line-table base and list ID remain unchanged. It derives the post-callback
visited fact from the actual write.

`OriginalLineMixed` uses current stamp memory at every iteration to choose a
duplicate skip or a fresh crossing callback. Its conditional `Admitted` domain
requires the fresh callback contract at each reached state. Any finite admitted
run has an original-instruction prefix bounded by `281 * n`, ends back at the
header, advances its list cursor by `2 * n`, and preserves ESP. A final sentinel
adds seven instructions through the actual iterator return.

This is a composition theorem, not yet the complete line-list invariant:
same-side rejection and early-stop callbacks are outside this domain. The
fresh contracts, capacity, list/geometry protection, callback target and parent
frame still need to be maintained across successive fresh entries. The sentinel
condition is currently supplied at the final reached state. No claim is made
that every reachable E1M1 list satisfies these obligations.

Kernel fixtures establish a nonvacuous fresh linedef-zero visit, followed by
the same ID as a duplicate and then the sentinel, for both trace-size branches.
Exactly one intercept is inserted. The CALL overwrites a deliberately unrelated
initial stack word with its real return address. The extraction manifest pins
fourteen original byte ranges, and strict axiom/mutation checks cover the new
transport, stamp and finite-loop proofs. No new native sampling is claimed;
these results compose the existing checked instruction semantics.

```sh
./scripts/lake build Doom.Proofs.OriginalLineMixed
python3 scripts/verify_original_line_dispatch.py
PYTHONPATH=tests python3 -m unittest test_original_line_dispatch test_original_line_crossing test_original_line_resume test_original_line_cell -v
```

## All line-callback outcomes in a finite traversal

`OriginalLineReject` connects fresh dispatch to the same-side rejection path.
Both side-test branches return success without producing an intercept, restore
the saved list cursor, advance it by two bytes, and return to the iterator header.
This path needs geometry and frame separation, but no fraction or intercept-array
capacity contract. The composed original-instruction bound is 178.

`OriginalLineStop` handles a crossing that requests early termination. It returns
zero through the iterator's parent frame, with ESP advanced by twelve bytes.
Explicit frame protection identifies the restored register and return address
with the words in the original memory. The stop contract imposes no requirement
on the unvisited suffix of the list.

`OriginalLineTraversal.Runs` combines sentinel return, duplicate skip, same-side
rejection, continuing crossing, and early stop. Every finite admitted traversal
has an original-instruction execution bounded by `281 * n + 7`, returns zero or
one, and restores the iterator stack frame. Here `n` counts visited non-sentinel
entries, including an early-stopping entry. `of_mixed` embeds the previous mixed
crossing/duplicate theorem's domain without adding per-entry assumptions.

This closes the callback-outcome coverage gap, not the reached-state invariant.
`Runs` still carries each fresh entry's geometry, separation and callback
contracts; it does not yet derive them from an initial E1M1 map/list encoding.
The stack theorem alone does not establish parent-frame memory protection.
Kernel fixtures exercise rejection, its newly stamped duplicate and the final
sentinel, and a terminal stop with an unmodeled later line ID, for both side-test
branches. The strict axiom and mutation checks reuse fourteen pinned original
byte ranges. No new native sampling is claimed.

```sh
./scripts/lake build Doom.Proofs.OriginalLineTraversal
python3 scripts/verify_original_line_traversal.py
PYTHONPATH=tests python3 -m unittest test_original_line_traversal test_original_line_dispatch test_original_line_crossing test_original_line_second_point -v
```

## Initial-memory invariant for rejection and duplicate scans

`OriginalLineInvariant` removes the per-reached-state contracts for a specific
complete class of line lists: every fresh entry is rejected by the side tests.
Its `Initial` contract refers only to the initial machine state, finite list,
geometry encodings and memory separation. It does not prescribe whether any
entry is already visited. `step` reads the current stamp memory each time,
including stamps written by earlier fresh rejections.

`Stable` preserves the cursor position, stack pointer and an explicit set of
protected words. `ready` derives the next fresh callback's complete contract
from that invariant and the initial geometry. `advance` proves preservation
through either the actual duplicate skip or the actual fresh rejection.
`walk` lifts this to an arbitrary finite prefix, with a `178 * n` instruction
bound. `through_sentinel` derives the final sentinel from the initial list image,
adds the actual seven-instruction return, and constructs `OriginalLineTraversal.Runs`.
There is no final-state sentinel or per-step geometry premise in that theorem.
`frame` and `parent_return` preserve protected initial words through the whole
scan and identify the final caller address and saved register with initial memory.

The protected words exclude mutable stamps unless a caller explicitly includes
them. The concrete fixtures cover a fresh linedef-zero rejection, its dynamically
recognized duplicate, and the sentinel, in both side-test branches. They also
protect the intercept cursor and parent frame. The kernel audit uses the same
fourteen pinned byte ranges; no new native sampling is claimed.

This is invariant closure for rejection/duplicate lists, not for arbitrary line
lists. Fresh crossings can insert records, change the intercept cursor and consume
capacity. Their representation/capacity invariant, early-stop integration into
that broader invariant, and its instantiation from the E1M1 map image remain open.
The static geometry/word-separation transport is intended for reuse there.

```sh
./scripts/lake build Doom.Proofs.OriginalLineInvariant
python3 scripts/verify_original_line_invariant.py
PYTHONPATH=tests python3 -m unittest test_original_line_invariant test_original_line_traversal -v
```

## Ordered collection and capacity through fresh dispatch

`OriginalLineDispatchAppend` transports the existing encoded intercept records
across the actual stamp write and indirect CALL. Its `live_append` theorem starts
with pre-dispatch memory, then reuses the side-test/fraction/append proofs to show
agreement with production `Collision.appendIntercept`: the old ordered prefix
survives, the new record is last, and the cursor advances by twelve bytes.

`OriginalLineCollection.Tracks` ties original memory and the cursor to the exact
production array, with a natural-number capacity reserve. The conservative bound
is `collected.size + remainingCandidates ≤ 128`. An append consumes one candidate
and adds one record; a duplicate or same-side rejection consumes a candidate
without adding a record. Thus a positive reserve derives the capacity required
for the next append. The invariant does not model original overflow behavior or
assert that every E1M1 query satisfies this sufficient bound.

`slots_apart` proves that distinct twelve-byte records among the 128 slots have
disjoint word writes, including when their base address wraps. `old_record_safe`
uses this theorem to derive the old/new-record separation needed by the append.
`Layout` still requires separation from callback/dispatch writes and the cursor
global. `append_execution` connects the collection transition to the actual
281-instruction-bounded original execution, its return to the list header and
its restored list cursor and stack pointer. `duplicate` and `rejected` preserve
the existing collection through those actual paths.

Concrete fixtures start with a nonempty collection, append a different hit in
both side-test branches, retain the original first record and recognize the
following duplicate. Mutation checks cover ordering, cursor advance, capacity,
geometry/branch assumptions and original bytes. The strict audit reuses fourteen
pinned ranges; no new native sampling is claimed.

This establishes the collection component of the mixed-loop invariant. Fresh
geometry, callback readiness and storage layout are still transition premises.
Joining their preservation with the initial-memory invariant, integrating early
stops and deriving the initial bounds/layout from the E1M1 map remain open.

```sh
./scripts/lake build Doom.Proofs.OriginalLineCollection
python3 scripts/verify_original_line_collection.py
PYTHONPATH=tests python3 -m unittest test_original_line_collection test_original_line_invariant test_original_line_traversal -v
```

## Initial-state mixed scans

`OriginalLineMixedInvariant` joins the list/geometry and ordered-collection
invariants. `Initial` records geometry and separation for a finite candidate
prefix in the original memory. Duplicate detection uses current stamp memory,
including stamps written by earlier visits. List words, geometry, callback target
and selected parent-frame words remain protected; stamps and the intercept cursor
are mutable. The initial collection is encoded, with a conservative capacity
reserve for every candidate visit.

`advance` derives callback readiness and storage separation from the invariant
and handles continuing visits, including negative fractions. `walk` composes
these visits when their initial geometry establishes continuation.
`through_sentinel` takes a separate initial sentinel premise; `parent_return`
recovers the success value, stack restoration, saved register and return address.
The separate continuation premise on this older interface is unnecessary for the
all-outcome scan below.

```sh
./scripts/lake build Doom.Proofs.OriginalLineMixedInvariant
python3 scripts/verify_original_line_mixed_invariant.py
```

## Initial-state scans with every callback outcome

`OriginalLineNoInsert` proves that negative-fraction and early-stop callbacks do
not write the intercept array or advance its cursor. It transports preserved
words across the actual stamp, CALL, side tests, fraction helper and return.
Separation from stack/scratch writes remains necessary; separation from a
hypothetical next record is unnecessary on these branches. Its collection lemma
preserves all existing records and releases one conservative reserve. The
negative-fraction lemma also connects to production `Collision.lineIntercept`.

`OriginalLineScan.scan_correct` now closes all five outcomes under the same
initial-memory invariant: dynamic duplicate, same-side rejection, negative
fraction, append, and early stop. A stop terminates recursion immediately. The
result records the actual number of visits, preserves the ordered collection and
protected memory, and either re-establishes the continuing invariant or proves
the original false return and restored parent frame. The abstract path's
`completed` flag is false on the stop branch.

`stopping_prefix` requires **no sentinel or suffix contract**. The prefix can end
at the stopping entry, with nothing assumed about later entries.
`through_scan` additionally accepts an initial sentinel after the candidate list;
it executes that return only if the whole list continues. Its original
instruction bound is `281*n+7`, with exact visited count, collection reserve,
return value and stack restoration. No reached-state geometry/readiness contracts
or per-entry continuation assumptions are supplied to either interface.
`stopped_parent` identifies the concrete saved register and return address when
those words belong to the protected initial footprint.

Kernel fixtures start with an existing hit and cover a negative intersection
with early-out enabled, short-branch and wide-branch stops with a non-sentinel
next word, and a previously stamped potential stopper. The earlier
append/duplicate/fresh-rejection fixtures continue to pass. Regressions reject
weakened branch, separation, prefix, sentinel and capacity premises, wrong
outputs and modified original bytes. The audit covers the 31 declarations across
the three modules and 15 extraction/execution certificates, reusing fourteen
pinned original byte ranges. No new native sampling is claimed.

This closes the callback-outcome cases for a **bounded, initially admitted line
scan**. The initial geometry, line IDs/pointers, valid-count state, storage
separation and conservative reserve still need to be derived from actual E1M1
query/map data. Original intercept overflow, thing iteration, the complete grid
loop, aim, firing, complete-tic and whole-game correspondence remain open.

```sh
./scripts/lake build Doom.Proofs.OriginalLineScan
python3 scripts/verify_original_line_outcomes.py
PYTHONPATH=tests python3 -m unittest test_original_line_outcomes test_original_line_mixed_invariant test_original_line_collection test_original_line_invariant -v
```

## Pinned E1M1 path-cell inputs

`E1M1PathMap` derives line-list non-sentinel entries, the terminal sentinel and
62-byte linedef pointer resolution from a BLOCKMAP word-image relation and the
actual list cursor. It preserves the leading linedef zero and repeated IDs,
matching the production loop's `#[0] ++ ids` visitation order. A separate theorem
uses `OriginalPathInit.ready` to establish an empty collection at the original
intercept-array base with enough reserve for any single E1M1 cell. Later cells
still require room for their candidates; this does not establish capacity for
the entire 64-step query.

The pinned data certificate checks all 828 cells in the 36×23 grid against the
3461-word BLOCKMAP: offsets and line IDs stay nonnegative under signed 16-bit loads,
all IDs are below the actual 475-line count, and every cell has at most 13 visits
including the leading zero. A reusable sequential-decoding lemma proves the per-cell indexed contracts
from the contiguous payload; the kernel checks that payload and the offset table
exactly. Python decoding and the WAD SHA256 remain the explicit extraction
boundary. The original loader's physical word image,
geometry/fraction readiness, grid-write preservation, valid-count/seen state
and later-cell capacity remain obligations before constructing `Initial`.

The older map-loader verifier retains `verify_original_line_scan.py`; the newer
traversal-outcome verifier is now `verify_original_line_outcomes.py`. Their
fixtures, tests and artifacts are separate, fixing a tooling-name collision.
The existing map-source verifier works with the restored loader helper again.

```sh
./scripts/lake build Doom.Proofs.E1M1PathMap
python3 scripts/verify_e1m1_path_map.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map test_original_line_scan test_original_line_outcomes -v
```

## Original lookup establishes the pinned cell's scan inputs

`E1M1PathMapLookup` connects the certified map words to the original eight
instructions at `0x2c541..0x2c55a`. Starting at lookup entry, its context represents
X/Y and width registers plus the two BLOCKMAP globals. The offset-table pointer
is the raw lump base plus eight bytes. The proof derives the offset read and its
signed-extension bound from the initial word image and certified cell, then
executes lookup to the scan header at `0x2c57f`.

The resulting contract establishes the exact list cursor, every ordered line ID,
non-sentinel entries, 62-byte linedef pointer resolution, and the final sentinel.
It also preserves all memory and SP. A separate collection theorem preserves
already collected hits, the append cursor and the existing capacity reserve;
lookup requires no additional slot. These conclusions use no post-lookup memory
or cursor premises. The production `pathCellInside` guard proves any selected
E1M1 row-major index is below 828, so the extracted certificate specializes the
join directly for every in-bounds coordinate, without a caller-supplied cell
selection equality.

The verifier rechecks the complete pinned BLOCKMAP certificate and extracts the
original lookup/list instruction bytes with their relocation records. All
transitive axioms remain within `propext`, `Quot.sound`, and `Classical.choice`.
The nonvacuous fixture uses an unaligned lump crossing address zero, repeated
linedef zero, line 474, and an existing intercept. Negative tests reject altered
bytes, wrong entry/count/cursor/header address, missing initial representation,
out-of-bounds admission, and increasing the capacity reserve without justification.

This removes the explicit scan-cursor premise at the lookup-to-scan boundary.
It does **not** establish the physical word image or lookup context from startup
and the preceding bounds/grid code. Loaded geometry, valid-count/seen state,
storage separation and capacity over later cells remain open, as does complete
aim-query correspondence. No new native sampling is claimed.

```sh
python3 scripts/verify_e1m1_path_map_lookup.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_lookup test_e1m1_path_map test_original_line_cell -v
```

## Bounds entry now establishes lookup and scan inputs

`E1M1PathMapBounds` starts at the actual line-iterator entry `0x2c520`, before
its two stack writes. It joins the original prologue, signed bounds decision and
BLOCKMAP lookup. For every in-bounds E1M1 coordinate, the extracted-byte
certificate reaches the scan header within 24 instructions and establishes the
ordered IDs, pointers and sentinel for the certified cell. The stack pointer is
exactly entry SP minus eight. The width register, lookup globals and retained
map image are derived across the prologue; no interior lookup context or
post-prologue image is supplied.

The two stack stores are not treated as harmless by assumption: entry-time
separation protects each required map/global word. The image transport reuses
32-bit read preservation for 16-bit words, so its conservative footprint includes
four bytes at each raw-word address. Existing intercept records and the append
cursor have their own protected footprints; the collection theorem preserves
exactly their previous capacity reserve and requires no empty-collection premise.

Outside cells are also covered. Negative X, negative Y, X at/above width, and Y
at/above height return true via the original epilogue within 16 instructions,
with SP advanced past the original CALL word and the original return PC. This
branch needs the initial bounds representation, but no map image, cell lookup,
line geometry or capacity assumptions.

The verifier checks three pinned original byte ranges (bounds entry, return,
and list lookup/iteration), the full prior E1M1 certificate, and the strict axiom
whitelist. The joined fixture preserves duplicate line zero and an existing
intercept with an unaligned lump crossing address zero. Separate outside cases
use a wrapping stack that overlaps the raw lump: the return branch remains
valid without a map-image premise. Mutation tests reject dropped separation,
wrong frame size/return value, incorrect entry/fuel, and altered original bytes.

Remaining: establish the iterator-entry word image, globals, coordinate/dimension
representation and separation from the loader and preceding grid caller. The
initial loaded geometry, valid-count/seen relation, callback storage protection,
later-cell capacity, thing iteration and complete aim query are still open.
This is a complete **bounds-to-scan-entry** connection, not a completed line
scan, grid loop or shot theorem. No new native sampling is claimed.

```sh
python3 scripts/verify_e1m1_path_map_bounds.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_bounds test_e1m1_path_map_lookup test_e1m1_path_map test_original_line_cell -v
```

## Grid caller now reaches the certified scan

`E1M1PathMapCaller` moves the map contract back to the actual grid gate at
`0x2ca7f`. The caller tests the line-traversal flag, installs the real callback,
copies X/Y from ESI/ECX into EAX/EDX, and pushes the real return PC. Its CALL
write is now included alongside both iterator-prologue stores in the protected
footprint (caller SP minus 4, 8 and 12). Dimension/global representations,
raw map words and existing intercept records are transported across those
writes; no interior iterator representation is re-assumed.

For enabled line traversal and an in-bounds cell, the caller, bounds decision
and lookup reach the certified ordered list at `0x2c57f` within 30 instructions,
with SP exactly caller SP minus 12. For an outside cell, the proof goes through
the original epilogue, returns to `0x2ca94`, and executes the caller's success
test to reach the thing gate at `0x2ca9c` within 24 instructions. Caller SP is
restored and EAX is one. This outside path needs dimensions and the enabled
flag, but no BLOCKMAP image or assumed callback result. It stops before thing
iteration.

The shared `first_scan_execution` theorem joins this prefix to the existing
pistol/shotgun execution from the post-sound firing boundary. The grid registers
and traversal-enable flag are derived from preceding code; the theorem does not
ask for them again. The complete joined prefix is bounded by 368 instructions.
Map dimensions, globals, image and separation remain explicit premises at the
first grid state. Establishing those from the loaded map and preserving them
through the earlier setup is still required. The joined program uses the
existing decoded firing/grid program and the added caller/lookup ranges.

The certificate checks the pinned DOS dispatch bytes and relocations, reuses
all three prior iterator ranges and the 828-cell WAD certificate, and audits the
new theorems transitively against the standard axiom whitelist. The concrete
fixture starts with deliberately wrong EAX/EDX/EBX, an unaligned map crossing
address zero, duplicate line zero and a nonempty intercept collection. All four
outside directions use a wrapping stack overlapping the map. Negative checks
reject a disabled traversal flag, wrong source registers, dropped CALL-write
protection, wrong return branch/SP, invented extra capacity and moving the map
image premise back to the firing entry without a preservation proof.

Remaining obligations include earlier map-image/global preservation, the loader
connection, initial line geometry and visited-state relation, callback storage
protection during the scan, later-cell capacity, thing iteration and the full
query. This is a caller-to-scan-entry result, not complete shot equivalence.
No new native execution sampling is claimed.

```sh
python3 scripts/verify_e1m1_path_map_caller.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_caller test_e1m1_path_map_bounds test_e1m1_path_map_lookup test_e1m1_path_map test_original_line_cell -v
```

## Traversal initialization now supplies the map and collection

`E1M1PathMapSetup` moves the map-memory contract back from the first grid gate
to `P_PathTraverse` entry (`0x2c8a0`). It composes existing frame theorems for
initialization, X-axis setup (including its absolute-value/division helpers),
the first intercept, Y-axis setup and the second intercept. A protected word
survives the complete sequence. The footprint lists the actual initialization
destinations and the union of potential later stack writes; it works for either
axis direction and stationary-axis branches. The later caller/prologue slots
are already included. Read protection is conservative: a map halfword uses the
existing four-byte protected-read contract.

`map_at_grid` derives dimensions, lookup/line-base globals, the raw word image
and the caller's stack-separation conditions from `MapInputs` at traversal entry.
No post-initialization or first-grid copy of those assumptions is supplied.
`initial_collection_at_scan` also joins the initialization cursor reset to scan
entry. Initialization intentionally overwrites the intercept cursor, so this
proof establishes its new value and preserves that value through later setup;
it does not try to preserve the old cursor. The empty collection and enough
reserve for the selected certified cell follow from initialization and the
cell-length bound. No empty-list or capacity premise is needed at the grid gate.

The shared pistol/shotgun firing theorem keeps the existing continuous prefix
from the post-sound boundary to scan entry (bounded by 368 instructions), now
with the earlier map contract. It concludes both the certified scan words and
the initialized empty intercept collection. Coordinates and traversal flags
still come from the preceding execution proof. This establishes the state at
the scan header, not execution of the callbacks or the complete query.

The verifier rechecks the seven setup/helper byte ranges alongside the four
caller/iterator ranges, the pinned E1M1 map certificate and the transitive axiom
whitelist. A diagnostic fixture uses an unaligned raw map crossing address zero,
a deliberately stale intercept cursor and a wrapping valid-count increment.
All nine combinations of negative/stationary/positive axis directions retain
the map and establish the expected direction slots. Mutation checks reject
dropped write separation, a map aliasing trace globals, wrong lookup data,
keeping the stale cursor, invented reserve, and moving the map contract back
before traversal entry without another preservation proof.

The outstanding memory boundary is now **before traversal entry**: connect the
loaded map image to this contract and preserve it through the earlier firing,
aim-query and ray setup. Initial line geometry, visited-state relation, callback
storage protection during the scan, later-cell capacity, thing iteration and
complete query correspondence remain open. This proof does not establish loader
reachability for the diagnostic fixture or universal shot/tic equivalence.

```sh
python3 scripts/verify_e1m1_path_map_setup.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_setup test_e1m1_path_map_caller test_e1m1_path_map_bounds -v
```

## Aim-query entry now supplies traversal map state

`E1M1PathMapQuery` moves the protected map contract to `P_AimLineAttack` entry
(`0x2bb80`). The existing 36-instruction execution proof covers the four register
saves, ray multiplications, aim-global writes, callback/flag arguments and the
actual traversal CALL. The new frame proof composes the saved-register and aim
setup write contracts. It derives the map state at traversal entry while also
transporting the later initialization/grid/caller separation requirements.

All protection premises are expressed using query-entry memory and SP. A
`withStack` helper only describes future write addresses; it is not an executed
state or an assumption about future memory. The proved ray SP displacement is
16 bytes and the traversal-entry displacement is 28 bytes. Later cursor
protection therefore uses query SP minus 88. The cursor's initial value remains
unconstrained because traversal initialization resets it. Protected map origins
also have a read-preservation theorem, usable by the geometric input bridge.

`query_execution` is independent of the weapon and probe angle. It can be reused
at a center, right or left probe entry that satisfies its contract; it does not
prove the intervening probe-selection logic or preservation between completed
queries. The shared first-shot scan theorem uses `MapInputs` at the first query
entry, deriving the later traversal and grid map states and retaining the
initialized collection conclusion. The continuous firing prefix still starts
at the post-sound boundary and has the same 368-instruction bound. Shooter,
angle/table and traversal-geometry encodings remain explicit obligations; this
memory transport does not discharge those geometric contracts.

The verifier checks two additional pinned original ranges (ray and aim setup),
alongside the prior eleven ranges and the E1M1 map certificate, and audits the
transitive axioms. The diagnostic fixture uses an unaligned map crossing address
zero, nonzero signed origins, an unaligned actor/table address and a stale aim
target. It checks the target reset and real callback/flag/return stores as well
as protected map/origin retention. Its diagnostic table values and entry state
are not claimed to arise from E1M1 startup. Negative checks reject map aliasing
with aim globals, dropped write protection, wrong frame offsets, incorrect
execution entry/length, stale target preservation and removing the earlier
firing-to-query boundary obligation.

Remaining: supply the map contract from the loaded map and preserve it through
firing and the bullet-slope caller before query entry. Connect the shooter/table
geometry, initial line geometry and visited-state relation; prove callback
storage preservation and later-cell capacity; then complete thing iteration,
query callbacks and the full shot/tic connection. No complete query or universal
behavioral/graphical correspondence is claimed here.

```sh
python3 scripts/verify_e1m1_path_map_query.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_query test_e1m1_path_map_setup test_e1m1_path_map_caller -v
```

## Map preservation now starts at post-sound firing entry

`E1M1PathMapFiring` connects the map contract across the actual pose setter,
ammo decrement, flash/light setters, aim CALL, bullet-slope register saves and
first geometry-query CALL. Both pistol and shotgun share the result. Its
`MapInputs` is expressed at the original post-sound firing state; the first-scan
join no longer assumes a map image at an intermediate aiming boundary.

The protected-word proof composes the existing setter/debit write footprints
with the real CALL and register-save stores. It proves that query entry is
24 bytes below the original SP, and transports later traversal/scan protection
from that layout. Cursor protection is correspondingly expressed at original
SP minus 112. The map may be unaligned and addresses wrap modulo 2^32, provided
the stated byte-separation premises hold. The theorem does not pretend the
whole memory is unchanged: player ammo, actor state, flash/light and stack
contents change as before.

`query_execution` joins the preservation proof to the actual bounded firing
execution (at most 127 instructions). `first_scan_execution` composes this with
the earlier query, traversal, axis setup and grid-caller proofs to reach the
first line-list scan within 368 instructions. It supplies the scan's map/list
facts and initialized empty collection. Weapon-state inputs, initial geometry,
layout, successful axis calculations and cell selection remain hypotheses.

The certificate pins the six added original code ranges (both firing routines,
actor setter, flash setter, light setter and bullet-slope routine), alongside
the prior map/query/traversal ranges. The diagnostic fixture combines real
weapon-table inputs with a small map image, both guns, zero and signed-boundary
ammo, unaligned player/actor/map addresses and a wrapping stack. These are
nonvacuous entry states, not a claim of reachability from level startup.

Remaining: establish the initial map contract from loading and preservation
through earlier sound processing; connect shooter/table and line geometry,
visited-state relation and callback storage; establish later-cell capacity and
finish query/tic correspondence. This is a protected-memory and executed-prefix
connection, not a completed aiming, firing or whole-game parity proof.

```sh
python3 scripts/verify_e1m1_path_map_firing.py
PYTHONPATH=tests python3 -m unittest test_e1m1_path_map_firing test_e1m1_path_map_query test_e1m1_path_map_setup -v
```

## Query-entry shooter data now supplies traversal geometry

`E1M1AimGeometry` removes the intermediate aim-setup and traversal-coordinate
premises from a new shared firing-to-scan join. Starting at query entry, it
requires the shooter x/y/z/height words, angle/range registers, the selected
sine/cosine samples, map origins and explicit address separation. It derives
the ray endpoint, actor reads, firing height, traversal coordinates and origin
reads used by the existing production-geometry proof.

`RaySamples` only requires the two table entries used by this query and the
cosine-table pointer. `samples_of_tables` obtains that smaller contract from
the existing full `ThrustTables` representation. The endpoint proof retains
DOOM's signed integer-map-unit range multiplication and 32-bit wraparound;
it does not substitute general fixed-point multiplication. The generic query
result is reusable at any probe entry satisfying these contracts, including
fallback probe angles. It does not yet prove preservation across a completed
probe or transport the shooter/angle/table values through earlier firing.

`path_inputs` derives the old traversal-init contract without assuming the
endpoint, coordinates or post-setup origin values again. Layout-only stack
states express the two setup write-separation contracts before execution;
map-origin protection and the argument-slot read protection are carried to the
actual traversal state. `query_path_correspondence` connects the result to an
executed prefix of at most 96 instructions through path initialization.
`first_scan_execution` feeds this into the existing at-most-368-instruction
pistol/shotgun prefix: map data is assumed at post-sound firing entry, while
shooter/table geometry is now assumed at first-query entry.

The verifier reuses the 19 pinned original code ranges and E1M1 map certificate
and audits every new theorem's transitive axioms. Diagnostic query states use
unaligned actors, nonzero signed origins, a negative shooter z, stale aim target
and directions at zero, quarter/half turns and the last unsigned angle. Their
selected values are tied to the production fine-angle table. These states are
not asserted reachable from startup; the theorem still requires the selected
table values to be present in DOS memory.

Remaining: derive the query-entry shooter pointer, angle, actor fields and
selected table reads from the earlier firing state; link initial map data to
loading and sound preservation; establish line/visited/callback relations and
later-cell capacity; finish the complete query and tic. No full aiming or
whole-game correspondence theorem follows yet.

```sh
python3 scripts/verify_e1m1_aim_geometry.py
PYTHONPATH=tests python3 -m unittest test_e1m1_aim_geometry test_e1m1_path_map_firing -v
```

## Firing entry now supplies shooter and aiming geometry

`E1M1FiringGeometry` transports the query-entry geometry contract through the
actual pose/debit/flash/light and bullet-slope setup. Both the map contract and
shooter/table geometry can now be supplied at the same post-sound firing entry.
The joined first-scan theorem no longer assumes an intermediate shooter,
angle, table, coordinate or map-origin encoding.

The proof follows the actual data flow: the flash setter preserves the player
register; the player-to-actor pointer survives the intervening stores; the aim
CALL loads that pointer; the actor angle survives the bullet-slope saves before
being read; and the first query receives that actor, angle and 1024-unit range.
Protected actor coordinates/height, the two selected trigonometric samples,
cosine pointer and map origins are transported to query entry by the existing
memory frame proof. This retains byte-level separation and 32-bit wrapping
addresses rather than silently assuming a disjoint machine memory.

The input contract states shooter words, table samples, origins and separation
at firing entry. Layout helpers derive the later aim and traversal write
addresses from the proved 24-byte query-entry stack displacement. A generic
`transport` theorem assembles geometry from explicit register/read-preservation
facts; the actual firing theorem discharges those facts, without unfolding the
large executed state separately in every geometry field.

`first_path_correspondence` joins the geometry to the actual prefix through
path initialization (at most 223 instructions). `first_scan_execution` supplies
the existing at-most-368-instruction scan prefix, map/list facts and initialized
empty collection. Successful axis calculations, inside-cell selection and the
weapon-state contract remain explicit. The certificate reuses the 19 pinned
original code ranges and audits the transitive axioms of all new declarations.
The diagnostic fixture exercises both weapons with unaligned player/actor/map
addresses, wrapping stack, ammo boundary cases, signed origins, a negative
shooter z and selected production table samples. It is not a loader-reachability
claim.

Remaining: establish the initial map/geometry representation from loading and
preservation through earlier sound processing; connect initial line geometry,
visited-state and callback storage; establish later-cell capacity and complete
the query and tic. The generic geometry transport is reusable, but this join
only covers the first query, not preservation across completed fallback probes
or the subsequent damage/pellet loop.

```sh
python3 scripts/verify_e1m1_firing_geometry.py
PYTHONPATH=tests python3 -m unittest test_e1m1_firing_geometry test_e1m1_aim_geometry -v
```

## First-scan line memory, trace and visit epoch

`E1M1ScanMemory` connects three memory facts to the same first-scan state used
by `E1M1FiringGeometry.first_scan_execution`:

- Protected words survive the actual pose/debit/flash, bullet-slope, ray,
  traversal initialization, axis setup, caller and lookup summaries. The
  eight loaded line/vertex words now have a common post-sound contract that
  transports to scan entry, including wrapping endpoint coordinates.
- The four trace words come from the initialized production `pathStart`,
  including Doom's block-boundary nudges. Their values survive the subsequent
  setup and iterator stores; the proof does not require initialization to
  preserve the old trace.
- The visit epoch survives the prefix before initialization, increments as a
  32-bit word, and survives through scan entry. Together with the map-derived
  selected line pointer and preserved line stamp, this proves the exact initial
  duplicate-test equivalence. It neither assumes all lines are fresh nor
  excludes epoch wraparound.

The shorter `BeforeInit` contract is intentional: the existing full `Safe`
contract cannot protect the old epoch through the instruction that increments
it. The proof separates preservation before initialization from preservation
of its newly written result. The diagnostic fixture checks both guns, an
unaligned loaded line/vertex representation and a wrapping stack, and derives
an epoch of zero from `0xffffffff`. These are explicit test states, not claims
that startup reaches them.

These facts concern the first-scan state expression. Reaching that state still
uses the existing execution theorem's weapon/map contracts, successful axis
calculations and inside-cell selection. The scan-wide correspondence between
DOS stamps and the production visited set is not yet proved: repeated IDs and
updates during callbacks remain to be connected. Callback scratch/record
storage, assembly of the mixed-scan initial contract, loader linkage, later-cell
capacity and the complete query/tic also remain open. No runtime behavior changed.

```sh
python3 scripts/verify_e1m1_scan_memory.py
PYTHONPATH=tests python3 -m unittest test_e1m1_scan_memory test_e1m1_firing_geometry -v
```

## Visited stamps now follow the entire bounded scan

`OriginalLineVisits` extends the mixed-scan invariant with the mutable DOS
line stamps. The additional `Layout` contract refers only to the initial scan
state: candidate IDs/pointers, stamp separation from callback stack writes,
and stamp separation from intercept-record storage. Distinct stamp words are
proved disjoint from the original 62-byte stride for IDs below 32768, even if
the line-array base wraps; this is not an extra pointer-injectivity assumption.

The initial layout and existing `Stable` invariant derive protection at each
reached callback. A fresh line receives the current epoch before its callback,
and retains that stamp through same-side rejection, negative fractions,
intercept insertion and early stop. Other stamps and the epoch are preserved.
Duplicates do not write memory. `duplicate_iff` connects the actual DOS branch
to the corresponding Boolean array read. `step_represents` connects a complete
machine iteration to the same `Array.set! id true` operation used in
`Collision.pathTraverse` in `Doom/Path.lean`.

`scan_represents` carries this relation through the existing dynamically stopping
scan. It marks exactly the examined prefix, so repeated IDs remain seen and an
early stop does not mark its suffix. `scan_execution` pairs the final array
relation with the existing original-instruction prefix, bounded by 281 times
the number of examined candidates. This reuses the previously proved callback
execution and mixed-scan contracts rather than introducing per-callback
post-state assumptions.

`firing_represents` supplies the initial relation from the preceding post-sound
memory/frame proofs. `fresh_represents` states the exact condition needed for
the live runtime's all-false initial array: every relevant DOS stamp differs
from the new epoch. A wrapped epoch alone cannot establish that condition; a
zero stamp and a zero epoch encode a seen line. Freshness/reachability therefore
remains explicit for arbitrary-length input histories. This is not a proof of
whole-query equivalence at counter wraparound, nor a claim that this diagnostic
state is reachable from the fixed E1M1 start.

Concrete fixtures join the theorem for the sequence `0, 0, 1` (crossing,
duplicate, rejection), and for negative intersections and both early-stop
geometry branches. They check the resulting bits and retain the existing
instruction-execution proof. Loaded geometry and callback scratch/record
storage must still be assembled into the mixed-scan initial contract at the
actual firing boundary. Later-cell capacity, cell stepping, the thing iterator,
autoaim clipping and the rest of the query/tic remain open. No engine behavior
changed in this proof-only step.

```sh
python3 scripts/verify_original_line_visits.py
PYTHONPATH=tests python3 -m unittest test_original_line_visits test_e1m1_scan_memory -v
```

## Firing supplies callback geometry and intercept storage

`E1M1ScanGeometry` joins three existing boundaries. Successful axis setup and
an in-bounds first cell derive the actual scan stack pointer as firing SP minus
124 bytes. The indexed callback view has firing SP minus 128 bytes. These are
32-bit modular equalities, so the reasoning does not silently assume that stack
subtraction cannot wrap.

The preserved line/vertex words and initialized trace now construct a shared
`Geometry` contract at each selected first-cell callback **template**. The map's
proved list lookup supplies the selected line pointer. The same geometry feeds
either same-side rejection or crossing, according to the production side test.
This is the pre-dispatch view used by the existing mixed-scan invariant; it is
not a claim that every listed candidate executes a callback. Duplicates and
early termination must still follow the scan's actual control flow.

`Storage` expresses byte separation once in terms of the original firing SP,
the line-array base, all 475 E1M1 line stamps, and the fixed 128 intercept slots.
`storage_layout` converts it to the collection's dispatch, side-test, scratch and
metadata protections at any selected index. No reached cursor or reached memory
contents are assumed. This is a conditional layout theorem; loader/allocation
and reachable-state facts still need to establish its initial separation.

`first_line_geometry` packages the original instruction prefix (at most 368
steps from the common post-sound pistol/shotgun boundary), first-cell list
facts, empty collection with reserve, derived SP, selected geometry template,
and intercept layout. It uses the already proved memory transport instead of
adding geometry assumptions at a reached callback.

The diagnostic fixture checks both side outcomes with firing SP=1, the wrapped
callback SP, all record/stamp pairs via bounds, and byte aliases at a record's
edge. Contract mutations reject missing initial geometry, protection, storage,
axis success and bounds, swapped trace coordinates/vertices, and wrong stack or
entry-PC claims. The certificate retains the original-byte/WAD checks and a
strict transitive axiom audit. No engine behavior changed.

Still needed for the complete firing-to-scan join: tail fraction/flag words,
the protected-read set, dispatch/stamp separation, the mutable-stamp layout and
initial freshness. Those must assemble `OriginalLineMixedInvariant.Initial`
and `OriginalLineVisits.Layout` before invoking the whole-scan theorem. Later
cells, thing traversal, clipping, complete queries and whole-tic observation
equality remain open.

```sh
python3 scripts/verify_e1m1_scan_geometry.py
PYTHONPATH=tests python3 -m unittest test_e1m1_scan_geometry test_e1m1_scan_memory -v
```

## The aiming line-scan contract is assembled

`E1M1ScanContracts.firing_active` derives the original early-out global's zero
value from the real aiming call's flags (`3`, lines plus things) and traversal
initialization. `firing_back` transports each back-sector null encoding from
post-sound memory. No reached-state flag value or back-sector value is supplied
to these transport theorems.

The module constructs scan candidates from ordinary line data, the selected ID,
and the production side test. Successful intersection fractions remain an
explicit pure-data obligation for crossing lines. Flags are fixed to the actual
aiming value, so `candidate_continues` proves that these callbacks cannot take
the solid-wall early-out branch. This does not imply that the later aiming
callback cannot stop while clipping ordered intercepts.

`protectedWords` generates the immutable read set: the saved callback word,
epoch and line-base globals, every list entry including the sentinel, and every
candidate's geometry/back-sector/early-out reads. The list protects a four-byte
window for each two-byte item, matching the existing memory invariant. Mutable
line stamps are tracked separately. `Protected` and `Layout` express byte
separation using the original firing SP, known list cursor and line-array base.
They derive the dispatch, side-test, scratch and intercept-array protections
used by the scan, rather than assuming protection at each reached callback.

`initial` now assembles every field of `OriginalLineMixedInvariant.Initial`.
`visit_layout` builds the accompanying mutable-stamp layout, reusing record/stamp
separation in the opposite direction. `scan_execution` connects this assembled
contract to the bounded original instruction prefix and the Boolean visited
array relation. `through_sentinel` additionally connects the continuing aiming
scan to its sentinel return, ordered intercept encoding and immutable-memory
preservation, without a caller-supplied per-line continuation condition.

The concrete diagnostic fixture has two occurrences of line zero. It checks a
crossing followed by a duplicate (one collected intercept), and a same-side
rejection followed by a duplicate (no intercepts). Both instantiate the complete
contract and original-instruction/sentinel theorem. The fixture uses an original
SP of 1, so its stack addresses wrap, and proves separation from all 475 stamps
and all 128 intercept slots. It is not a reachable-startup-state claim.

The assembly theorem currently starts at scan entry. Its geometry templates can
come from `E1M1ScanGeometry`; its flags and back encodings now have firing-entry
transport lemmas. Still join those facts in one common firing-entry wrapper,
derive the scan cursor and saved callback word there, and establish the static
layout and successful fractions from the loaded map/reachable state. Initial
visited-array freshness, later-cell capacity, thing scanning, grid stepping,
ordered-intercept clipping and complete query/tic correspondence remain open.
No runtime behavior changed.

```sh
python3 scripts/verify_e1m1_scan_contracts.py
PYTHONPATH=tests python3 -m unittest test_e1m1_scan_contracts test_e1m1_scan_geometry -v
```

## Firing entry now reaches the first-cell sentinel

`E1M1FiringScan` joins the assembled scan to the common post-sound boundary of
`A_FirePistol` and `A_FireShotgun`. `caller_cursor` derives the actual list address
from the protected BLOCKMAP image and selected offset. `caller_target` derives
the saved callback word (`0x2c5f0`) from the caller and iterator prologue.
`boundary` transports those facts through firing, aim setup and grid setup.

Its `Inputs` record contains firing-entry memory encodings, successful axis and
line-fraction computations, and static byte separation. `initial` derives the
complete mixed-scan invariant: callback geometry, generated candidates, flags,
back-sector tests, list facts and intercept-storage layout. It requires no
reached scan register or callback-address assumption. Side-test protection is
reused from the generated read set rather than specified a second time.

`firing_program` identifies the setup's decoded program with the existing
line-cell program. `firing_through_sentinel` consequently joins setup and the
complete first-cell line scan under one instruction map. The bound is
`375 + 281 * c.ids.length`; the result retains the scan's ordered intercept
encoding and traversal relation. The empty collection is derived from traversal
initialization. No per-candidate continuation premise is supplied: aiming uses
flags 3, so the early-stop flag is absent.

This is a conditional local execution theorem. It does not yet establish those
input contracts from startup or all reachable firing states. It does not assert
the precise restored parent return PC, full `Collision.pathTraverse` equality,
all cells, things, aim clipping, complete query/tic, or audiovisual parity.
The original sentinel instructions execute; preserving their caller's saved
return words through callbacks is a separate remaining obligation.

```sh
python3 scripts/verify_e1m1_firing_scan.py
PYTHONPATH=tests python3 -m unittest test_e1m1_firing_scan test_e1m1_scan_contracts -v
```

## First-cell line return now reaches the thing gate

`E1M1ScanReturn` closes the saved-frame gap after the first-cell line scan.
`protect` extends the mixed-scan invariant's immutable-word set, while
`protect_finished` proves that this extension changes neither execution nor the
pure scan result. This helper can be reused for other caller-owned words.

`prologue_words` and `caller_words` derive the saved EDI and return PC from the
original PUSH/CALL instructions. `firing_frame` places those values at the actual
first-scan frame. `ReturnSafe` requires separation of the two words at original
firing SP minus 120 and minus 116 from line stamps, intercept records and cursor
metadata. `stack_protected` derives separation from every callback stack write,
including modular wraparound, without another stack-layout premise.

`framed` adds those words to the existing scan invariant. `parent_return` proves
that the sentinel returns EAX=1, restores SP to firing SP minus 112, restores EDI
to its pre-iterator grid value, and returns to **0x2ca94**. The return PC is written
by the original caller and preserved through callbacks; it is not a reached-state
assumption. `firing_to_things` then executes the original two-instruction success
test, reaching **0x2ca9c**, the thing-iterator gate, under one continuous decoded
instruction prefix bounded by `377 + 281 * c.ids.length`. Intercept encoding and
order survive that test because it performs no memory writes.

This theorem stops before executing the thing gate or thing iterator. The new
heap/metadata separation must still be derived from loaded-map and reachable
firing-state facts, alongside the existing input contracts. Remaining cells,
thing intersections, aim clipping, shot damage and complete query/tic or
observable correspondence remain open. No runtime behavior changed.

```sh
python3 scripts/verify_e1m1_scan_return.py
PYTHONPATH=tests python3 -m unittest test_e1m1_scan_return test_e1m1_firing_scan -v
```

## The thing gate now makes the original CALL

`E1M1ThingGate` derives the option word `3` from aim setup and preserves it through
setup, the iterator prologue and the complete first-cell line scan. `flagged`
reuses the generic immutable-word extension from `E1M1ScanReturn`;
`flagged_finished` proves that this changes neither the executed scan nor its
pure result. `FlagSafe` states separation of the option word at original firing
SP minus 48 from line stamps, intercept records and cursor metadata. Separation
from callback stack writes is derived, including modular wraparound.

`enabled` combines the preserved word with the restored caller SP. It proves
that the original thing gate sees bit 2 and takes its CALL branch. `firing_call`
joins this six-instruction gate/setup/CALL to the previous continuous prefix.
Both weapons reach **P_BlockThingsIterator at 0x2c5a0**, with callback **0x2c720**,
return PC **0x2cab1**, and SP equal to firing SP minus 116. The bound is
`383 + 281 * c.ids.length` instructions. The arguments are the actual gate ESI
and ECX values copied into EAX and EDX by the original code.

`call_collection` proves that the CALL preserves existing intercept records,
the append cursor and the same capacity bound. The firing join derives the CALL
word's separation from the saved-return-word protection already required by the
previous theorem; it does not introduce another independent collection premise.

This does **not** yet prove that the retained ESI/ECX values identify the intended
map cell. That requires register-restoration lemmas through each callback outcome
and the scan loop. The thing iterator's bounds tests, list lookup and body have
not been executed by this theorem. Initial memory contracts and flag separation
remain conditional on loaded-map/reachable-state facts. Full aiming, shot damage,
complete query/tic and audiovisual parity remain open. No runtime changes.

```sh
python3 scripts/verify_e1m1_thing_gate.py
PYTHONPATH=tests python3 -m unittest test_e1m1_thing_gate test_e1m1_scan_return -v
```

## The thing CALL now receives the intended cell

`OriginalLineCoordinates` proves that the line callback saves ECX and ESI in
its actual prologue, preserves those words through both point-side helpers,
and restores the registers on rejection and crossing returns. Crossing includes
the fraction helper and optional intercept writes. The existing scan storage
and cursor layout already separate those writes from the saved coordinate
slots; no new coordinate-preservation premise is added.

That local result lifts through duplicate skips, rejected lines and crossing
lines to the entire mixed scan and its sentinel epilogue. The scan induction
reuses its existing `Stable` invariant and capacity argument rather than
assuming properties at each reached callback. The generic result is independent
of the E1M1 firing wrapper and can serve later cells as well.

`E1M1ThingCoordinates` then connects the restored registers to the production
path's `startBlockX` and `startBlockY`, including original block-boundary
nudges. Its `firing_call` strengthens the preceding continuous execution result:
from the common post-sound firing state, the original code reaches
`P_BlockThingsIterator` at `0x2c5a0` with those coordinates in EAX/EDX, callback
`0x2c720`, stack pointer minus 116, return PC `0x2cab1`, and the unchanged ordered
line-intercept collection. The bound remains `383 + 281 * list_length` for
both pistol and shotgun, under the same firing, flag and return-frame contracts.

The thing iterator's body, bounds checks and linked-list lookup have **not**
yet been executed in this proof. Loaded-map/reachable-state input discharge,
later cells, clipping and damage remain open. This does not establish full
aiming, firing, or whole-tic equivalence.

Validation includes a wrapping-stack fixture with different nonzero ECX/ESI
values, crossing/duplicate and rejection/duplicate outcomes, and tests rejecting
swapped coordinates, wrong save/restore slots, missing separation and incorrect
CALL targets. The fixture is diagnostic, not a reachable-state proof.

```sh
python3 scripts/verify_e1m1_thing_coordinates.py
PYTHONPATH=tests python3 -m unittest test_e1m1_thing_coordinates test_e1m1_thing_gate -v
```

## Original thing bounds and first pointer lookup are connected

`OriginalThingEntry` pins three additional ranges from the shareware 1.9
executable: `0x2c5a0–0x2c5bf` (prologue and signed bounds),
`0x2c5c0–0x2c5d1` (first pointer lookup and null test), and
`0x2c5e2–0x2c5ea` (successful return). Extraction checks the executable hash,
file mapping, bytes and data-object relocations. Kernel-checked decoding and
instruction execution cover every state admitted by the existing flat-memory
machine model, including aliasing and modular addresses.

The iterator saves its callback on the stack, tests signed X/Y against the
map dimensions, and loads a 32-bit head pointer from `blocklinks[x+y*width]`.
Out-of-bounds or empty cells return true. A nonempty cell stops at `0x2c5d2`,
before the object pointer is copied into EAX and the callback is invoked.
The natural/signed bounds bridge and index proof reuse existing line-iterator
lemmas. The new prologue's sole store is proved to preserve existing line
intercepts using the prior return-frame array separation.

`E1M1ThingEntry.firing_lookup` joins this prefix to both weapons' existing
post-sound firing proof. Width, height, the object-table global and the selected
head word are transported from that common starting memory through setup, the
mixed line scan, the thing CALL and its prologue. Its new `ReadSafe` contract
states initial address separation; it does not assume read values at a reached
iterator. The existing scan preservation extension handles the additional reads.

Under those explicit contracts, the bound is `403 + 281 * list_length`.
A nonempty selected head reaches `0x2c5d2` in EDX with saved callback `0x2c720`
and SP minus 120. An empty head returns true to `0x2cab1` with SP minus 112.
Both branches retain the ordered line-intercept collection. This executes only
the first object-table lookup, not any object callback or list traversal.

The dynamic head encoding and its separation still need to follow from the
reachable object-list representation. The remaining firing inputs also retain
their earlier explicit assumptions. This is not full aiming, firing or whole-tic
correspondence. Closed diagnostic fixtures exercise signed edges, empty and
nonempty lists, unaligned pointers, and wrapping stack/table addresses; they do
not establish reachability from startup.

```sh
python3 scripts/verify_e1m1_thing_entry.py
PYTHONPATH=tests python3 -m unittest test_e1m1_thing_entry test_e1m1_thing_coordinates -v
```

## Original object callback handoff is connected

`OriginalThingCallback` pins two additional ranges from the same authenticated
shareware 1.9 executable: `0x2c5d2..0x2c5e2` and `0x2c720..0x2c72b`.
Their decoded instruction proofs establish three connected pieces:

- The iterator passes its current object in EAX, reads the indirect callback
  target before pushing the real return word `0x2c5d7`, and enters the callback.
- Six register saves and local allocation preserve the list pointer at
  callback-entry ESP minus 12, preserve the return word, and copy the object
  argument to ECX. Protected reads and existing intercepts survive the writes.
- After the callback, zero EAX selects the false-return path without advancing
  EDX. Otherwise the iterator reads `[EDX + 44]` from the **current** memory and
  selects the next callback or the successful empty-tail return. This does not
  assume the callback left that link unchanged.

`E1M1ThingCallback.firing_enter` joins the first two pieces continuously to the
common post-sound firing contract for either weapon. For an explicitly nonzero
selected head, it reaches the intersection body at `0x2c72b` within
`413 + 281 * list_length` modeled instructions. ESP is firing-entry ESP minus
172; the saved object and callback return word are at minus 136 and minus 124.
The previously collected line intercepts and their cursor remain encoded.
Separation for the seven stores is stated relative to the initial firing stack,
not supplied as an assumption about the reached callback state.

This discharges the iterator-to-object-callback ABI seam in the eventual
hitscan/tic proof. It does **not** prove the object intersection calculation,
callback epilogue, list traversal, reachable-state discharge of the memory
contracts, or all-input gameplay/rendering correspondence. No runtime changed.

Validation: `python3 scripts/verify_e1m1_thing_callback.py` authenticates the EXE,
checks pinned ranges and the strict transitive axiom audit. The targeted tests
reject altered bytes/file offsets/relocations, missing target or stack
separation, incorrect object/return offsets, wrong branch destinations and an
incorrect link field. Kernel-evaluated diagnostic fixtures cover wrapping and
unaligned stacks, null and nonnull links, and a callback-modified link. These
fixtures are not claims about reachable gameplay states or independent native
execution. Reports are in `artifacts/e1m1-thing-callback/`.

## Original object diagonal and first-side calculation

`OriginalThingDiagonal` pins `0x2c72b..0x2c78d` from the same authenticated
shareware 1.9 executable. The instruction proof covers the signed XOR comparison,
SETG/byte mask, both diagonal-construction branches and the first point-side CALL.
The branch is strictly greater than zero; equal trace deltas select the
nonpositive branch. The additions/subtractions retain 32-bit wraparound.
`live_diagonal` relates all four endpoint coordinates to the production
`Collision.thingIntercept` expression via the definitional `production` theorem.
The existing function is now public for proof access; its body is unchanged.

`OriginalThingFirstSide` reuses the complete `OriginalDivlineSide` proof. Its
`helper_inputs` transports trace memory through the scratch store and CALL and
supplies the helper's register/memory contract. Its `live` theorem proves the
first endpoint's exact Boolean side result, real return to `0x2c78d`, restored
stack/object pointer and preserved second-endpoint Y coordinate. The unconditional
`second_endpoint` theorem also preserves the saved second-endpoint X word for
the next CALL. Protected reads
survive the scratch store, CALL and four helper saves, including wrapping stacks.

`E1M1ThingFirstSide.firing_first_side` extends the continuous first-cell firing
execution for either weapon to that helper return within
`480 + 281 * list_length` modeled instructions. Previously collected line
intercepts remain encoded. All new collection separation is expressed relative
to the initial firing stack. This execution join does **not** discharge the
separate geometric theorem's object/trace representation contract: that transport
must still be derived from firing entry and ultimately from reachable states.
Do not read the joined execution theorem as a complete first-object semantic join.

The next work is that representation transport and the second endpoint side
call/crossing decision, then the intersection fraction and collection/return.
No complete object-intercept, query, tic or audiovisual correspondence is claimed.

Validation entry points are `python3 scripts/verify_e1m1_thing_first_side.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_thing_first_side -v`. Checks include
byte/relocation authentication, strict transitive axiom audits, rejected mutations
of input/separation premises, endpoint/return addresses, fraction filtering and
firing bounds. Kernel-evaluated synthetic fixtures cover signed-XOR zero, both
sign branches, coordinate overflow, axis-aligned traces and wrapping/unaligned
stacks; these are not reachable-state proofs or native-emulator cross-checks.
Artifacts are in `artifacts/e1m1-thing-first-side/`.

## Original object second side and crossing gate

`E1M1ThingGeometry.callback_inputs` transports object x/y/radius from common
post-sound firing entry and the initialized shot trace from `firstScan`. The
complete first-cell line scan, iterator and object callback preserve those
words under explicit original-state separation contracts. The trace is derived
from initialization, rather than assumed equal to the old globals at firing
entry. `firing_live` joins the first endpoint result to this earlier boundary.

`OriginalThingSecondSide` decodes the additional DOS bytes `0x2c78d..0x2c7ae`,
saves the first side result at SP+16, loads the preserved second endpoint and
reuses the full `OriginalDivlineSide` proof for the second CALL. It proves the
saved first result survives that helper, then proves the actual CMP/JNE branch.
Equal sides select `0x2c805` and EAX=1; the definitional production equation proves
`Collision.thingIntercept trace target = .ok none`. Unequal sides select
`0x2c7ae`, where fraction calculation begins. No fraction result or successful
object append is asserted by this theorem.

`E1M1ThingCrossing.firing_crossing` joins that branch to either weapon's common
post-sound entry in at most `533 + 281 * list_length` modeled instructions while
preserving the collected line intercepts. Reached-state geometry comes from the
entry contract, rather than new callback hypotheses. That contract still
requires initial object/map encodings, successful setup and memory separation;
discharging them for all reachable E1M1 states remains work. The fraction,
negative-fraction rejection, object append, epilogue and full object list are
next. Later cells, aim clipping, damage and complete tic/observable equivalence
remain open.

Validation entry points are `python3 scripts/verify_e1m1_thing_crossing.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_thing_crossing -v`. The certificate
chain authenticates 26 original code ranges and the existing 828-cell map image,
and audits every new theorem transitively. Negative contracts reject dropped
entry safety, confusing old and initialized trace, wrong endpoint/saved-side
slots, swapped branch outcomes, altered bounds and an incorrect no-hit result.
Synthetic kernel-evaluated states exercise equal/unequal sides, reversed
orientation, zero XOR, axis traces and wrapping stacks. They are diagnostic
fixtures, not reachable-state proofs or native-emulator tests. Artifacts are in
`artifacts/e1m1-thing-crossing/`.

## Original object fraction and rejection/insertion boundary

`OriginalThingFraction` authenticates `0x2c7ae..0x2c7da`, constructs the local
object divline from the saved diagonal endpoints and reuses
`OriginalInterceptVector` for the complete helper call. The model includes the
original return word, scratch stores and helper stack writes. The exact EAX
fraction follows from the actual production `Collision.interceptVector` result;
its successful result supplies the helper's IDIV safety obligation. No new
arithmetic solver or axiom is introduced.

`OriginalThingFractionInputs` proves that the first endpoint registers, second
endpoint register/stack word and trace survive both side calls and the crossing
decision. Thus the fraction's inputs derive from callback entry, instead of
being assumed independently at `0x2c7ae`. `OriginalThingFraction.production`
connects the same diagonal and the strictly negative filter to the actual
`Collision.thingIntercept` expression. A fraction of zero proceeds to insertion.

`E1M1ThingFraction.firing_fraction` connects all of this to either weapon's common
post-sound entry. Within `613 + 281 * list_length` modeled instructions, its
`Outcome` pairs the production optional hit with the exact rejection/insertion
PC and EAX. Equal-side rejection remains at `0x2c805`; a negative fraction reaches
`0x2c7da` with EAX=1; an accepted fraction reaches `0x2c7e4` with its exact raw bits.
All previously collected line records and their cursor remain preserved. Record
insertion itself and either callback epilogue are not executed by this theorem.

The additional contracts are original-stack separation for the local divline
and helper writes, and successful production arithmetic when the endpoints
cross. Initial map/object representation, separation, computation success and
freshness still need reachable-state discharge. The next work is the object
record append, epilogue and full linked-list traversal, followed by later cells,
ordered interception, clipping, damage and the complete tic/observable relation.

Recheck with `python3 scripts/verify_e1m1_thing_fraction.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_thing_fraction -v`. The strict
certificate audits every new theorem, 27 authenticated code ranges and the
existing 828-cell map image. Mutation checks reject changed endpoint addresses,
return addresses, fractions, negative-filter boundaries, removed memory or
arithmetic contracts and changed execution bounds. Kernel-evaluated synthetic
states cover positive/negative/zero fractions, both axis traces, same-side
rejection, zero denominator and wrapping stack writes. They do not assert that
those diagnostic states are reachable E1M1 states. Artifacts are in
`artifacts/e1m1-thing-fraction/`.

## Original object append, return and list continuation

`OriginalThingFinish` authenticates `0x2c7da..0x2c80f`, covering both epilogues
and the seven insertion instructions. Accepted hits write the fraction, zero
object-kind flag and original actor pointer into a twelve-byte record, then
advance the cursor once. The machine theorem retains aliasing behavior. The
ordered-collection theorem derives old/new record separation from the bounded
array, preserves earlier records and reuses the actual production append theorem
under the explicit `<128` capacity contract.

`E1M1ThingReturn.view_saved` proves that callback saved words survive both side
helpers, fraction setup and arithmetic. The epilogue reads the saved return word
at SP+48 and object cursor at SP+36 and restores SP by 52 bytes. Under separation
from an inserted record, `execution` joins the original RET to the existing
iterator continuation. The iterator reads the link at restored-object+44 from
post-callback memory and branches to the next-object CALL or end-of-list path.
This statement deliberately does not replace the post-callback link with an
initial-memory hypothesis.

`E1M1ThingFinish` proves that the complete preceding mixed line scan contains
only line intercepts, then derives a resolver that keeps linedef pointers for
those records and uses an object-ID mapping for object records. This avoids
incorrectly applying the old linedef-only address formula to an actor hit. Its
`collect` expression is the object-loop fragment using actual production
`Collision.thingIntercept` and `Collision.appendIntercept`; it is not a theorem
about the entire surrounding `pathTraverse` loop.

`firing_finish` joins one object visit to either weapon's common post-sound entry
in at most `633 + 281 * list_length` modeled instructions. The final state has
the matching optional append, restored iterator stack and exact next-link branch.
The actor's encoded coordinates, prior scan, object lookup and callback entry
are provided by the earlier joined proofs. Additional original-state contracts
supply object-ID/pointer mapping, one free record and saved-word separation from
array writes. No reached-state return address or object cursor is added as a
hypothesis. Initial encoding, arithmetic success and layout contracts still
require loaded-map/reachable-state discharge.

Next compose the linked-list invariant across every object visit, then execute
the iterator's own epilogue and return to grid traversal. Later cells, the
64-iteration cap, whole-traversal capacity, ordered interception, clipping,
damage and complete tic/observable correspondence remain open.

Recheck with `python3 scripts/verify_e1m1_thing_finish.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_thing_finish -v`. The strict
certificate audits every new theorem and 28 authenticated executable ranges,
retaining the pinned 828-cell image. Contract mutations check record kind,
pointer, cursor stride, capacity, saved-word offsets, the mixed resolver,
post-callback memory and the joined execution bound. Synthetic kernel-evaluated
fixtures cover accepted, zero and rejected fractions, prior-record preservation,
register restoration, wrapping helper stacks, null/non-null links and an
intentional link/record alias. The alias fixture is diagnostic; it does not claim
that such an object layout is reachable in E1M1. Artifacts are in
`artifacts/e1m1-thing-finish/`.

## Finite object-list traversal and iterator return

`E1M1ThingVisit` reuses the earlier instruction proofs at any object-list CALL
site. `entry_inputs` derives the geometry contract through the real indirect
CALL and prologue. `body` reuses both side tests and the intersection arithmetic;
`execution` joins the optional append, callback epilogue and next-link decision
within 230 modeled instructions. `frame` accounts for every callback stack and
array write, so subsequent visits can reuse protected memory facts.

`E1M1ThingList.Layout` records static separation, nonzero actor pointers,
ID-to-pointer mapping and arithmetic success. `Image` records the trace and
object encodings, the finite linked order, the callback slot and the saved caller
word. These are initial contracts, not per-visit execution/outcome assumptions.
The induction derives each visit's inputs, transports the image through its
writes, and uses the actual post-callback link to select the next node. The
collection grows by at most one per visit. A single capacity hypothesis,
`initial_collected.size + nodes.length ≤ 128`, therefore supplies every append.
This is conservative: rejected nodes also consume a reserved slot in the bound.

`E1M1ThingTraversal.execution` executes the already-authenticated iterator
return instructions at `0x2c5e2..0x2c5eb`. The complete list suffix takes at most
`230 * node_count + 3` instructions, returns EAX=1, restores SP by eight bytes
relative to the list-head seam, and jumps to the protected caller word at SP+4.
It includes an empty-list case. No new executable ranges were required.

`objectCell_collect` proves that the recursive collector equals an array loop
with the same scene lookup, intersection and append operations used in
`Collision.pathTraverse`. `execution_cell` joins that equality to the original
machine prefix and final encoded collection. This is still an extracted
object-cell fragment, not a theorem about the surrounding `pathTraverse`
control flow. It retains list order, including equal-fraction hits, and does
not add sorting or deduplication.

The previous firing-entry theorem remains intact. This new reusable list theorem
starts at its iterator seam; the whole-list image/layout and scene-ID relation
still need transport from the firing-entry scene and ultimately reachable-state
discharge. Caller coordinate/register invariants, the outer grid walk, later-cell
capacity, ordered interception, aim clipping, damage and whole-tic/observable
correspondence remain to be joined. The arithmetic-success and non-overflow
contracts are not claims about all possible original states.

Recheck with `python3 scripts/verify_e1m1_thing_traversal.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_thing_traversal -v`.
The strict audit extends the existing 28 authenticated code ranges and pinned
828-cell image. Contract mutations cover initial encodings, layout, whole-list
capacity, protected links, scene lookup, return address, stack delta and execution
bounds. Kernel-evaluated fixtures cover a three-node hit/reject/equal-hit list,
record order and contents, an unaligned wrapping stack, empty-list return,
invalid scene ID and overflow rejection. They are diagnostic states, not a
claim of reachable E1M1 execution. Artifacts are in
`artifacts/e1m1-thing-traversal/`; runtime behavior is unchanged.

## Firing entry to complete first-cell object traversal

`E1M1ScanCapacity` proves an upper bound of one new intercept per line candidate
on every branch of the mixed scan, then lifts it through the full scan from its
initialized empty collection. `E1M1ThingListInputs.capacity` uses the initial
candidate counts to supply the existing list theorem's reserve. The shared bound
is `c.ids.length + nodes.length ≤ 128`; it conservatively counts duplicate,
negative-fraction and same-side candidates that do not actually append.

`E1M1ThingListInputs.Data` contains object coordinates/radii and links at the
original post-sound firing state, their read separation, ID-to-pointer mapping,
static storage separation, nonzero pointers and arithmetic-success conditions.
It does not contain a reached machine state, callback outcome or list image.
`entry_read` transports ordinary fields through the complete setup, line scan,
thing CALL and iterator prologue. Trace words use a separate transport from
actual path initialization, preserving the original boundary nudge. `geometry`
and `linked` derive the complete list's representation at the iterator seam.
The static layout is rebased using the caller-derived stack position.

`E1M1FiringThings.saved_words` derives the callback pointer and caller return
word from the original CALL/prologue instructions, rather than requiring them
in initial memory. `image` assembles the list image from those stores and the
transported geometry and links. `execution` joins the prior firing prefix to
all list visits and the iterator epilogue. Its empty-list case uses the existing
iterator return directly, avoiding an extra epilogue after return.

`execution_scene` also relates the encoded node sequence to the selected cell
in the production scene's link array, with the correct row-major width and
object-ID lookups. From either gun's common post-sound entry it reaches
`0x2cab1`, EAX=1 and SP=`initial_SP-112`, within
`406 + 281 * line_candidate_count + 230 * object_count` modeled instructions.
The final mixed array contains the same ordered intercepts as the object-cell
fragment, including equal-fraction ties. The fragment uses the production scene
lookup, `thingIntercept` and `appendIntercept`; correspondence for the enclosing
`Scene.pathTraverse` cell walk has not yet been established.

Remaining initial hypotheses still need loaded-map/reachable-state discharge:
map and object encodings, linked-list and scene relations, static separation,
successful arithmetic and the conservative candidate-count bound. The next
connection is the caller register/frame facts and success test leading into
grid stepping, followed by later cells and traversal-wide capacity. Portal/target
clipping, damage, preceding sound preservation and complete query/tic/observable
correspondence remain open. This closes a continuous first-cell collection path,
not the complete aim query or weapon discharge.

Recheck with `python3 scripts/verify_e1m1_firing_things.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_firing_things -v`.
The strict audit reuses the same 28 authenticated DOS ranges and pinned 828-cell
image. Contract mutations exercise candidate-count capacity, protected reads,
initial geometry/link data, actual saved words, scene-cell width/ID mapping,
stack delta, return PC and the continuous execution bound. Kernel fixtures
exercise non-sorted scene IDs, equal-fraction order, empty/missing cells, invalid
actor IDs and exact/overflowing capacities. These are diagnostic cases, not an
independent emulator comparison or reachable-state proof. Artifacts are in
`artifacts/e1m1-firing-things/`; no runtime behavior changed.

## First-cell coordinates and caller success

`E1M1ThingPreservation` proves the two grid-coordinate registers (ECX and ESI)
are saved by the actual object callback prologue and restored by its epilogue.
The saved words survive both side tests, fraction calculation and optional
intercept insertion. The existing callback stack-separation contract protects
them; the proof adds no layout or reached-coordinate assumptions. The same
list-image transport used for collection correctness lifts this property
through an arbitrary finite node list and the iterator epilogue. Bounds checking,
head lookup and empty-list return also preserve both coordinates.

`E1M1FiringCellReturn.boundary_coordinate` connects these registers to the
production path's initialized first block via the preceding line-scan proof.
`firing_coordinate` retains them through the complete object list.
`success_test` executes the authenticated two-instruction TEST/JZ at `0x2cab1`.
The success value derived by the iterator selects `0x2cab5`, preserving every
register and memory byte across this test. Zero would select the abort branch
`0x2cb0b`; success is not inferred merely from reaching the return address.

`execution` joins those facts to either weapon's common post-sound entry. Its
bound is `408 + 281 * line_candidate_count + 230 * object_count`; its outputs
include EAX=1, SP=`initial_SP-112`, the correct initial cell in ECX/ESI, and the
same selected-scene ordered intercept collection. Both empty and nonempty lists
are covered. This reaches the grid-step boundary; it does not execute grid
stepping or establish correspondence of the complete `Scene.pathTraverse` loop.
The remaining grid-step registers/locals must be preserved too, and the original
initial encoding, arithmetic, separation, finite-list/scene relation and capacity
hypotheses still need reachable-state discharge.

Recheck with `python3 scripts/verify_e1m1_firing_cell_return.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_firing_cell_return -v`.
The strict transitive audit retains the same 28 authenticated DOS ranges and
828-cell map image. Contract mutations check incorrect saved slots/registers,
missing collection/layout/capacity inputs, wrong branch/PC/instruction count,
wrong output coordinates and scene width. A kernel-evaluated diagnostic fixture
uses distinct nonzero coordinates, a wrapping unaligned stack, a hit/rejection/hit
list and empty-list and success/failure cases. It is not an independent emulator
comparison or reachable-state proof. Artifacts are in
`artifacts/e1m1-firing-cell-return/`; runtime behavior is unchanged.

## Collection-preserving grid advance

`E1M1AdvanceCollection.memory` identifies the full resulting memory on every
endpoint/X/Y/stall branch. `frame` preserves any word disjoint from the only
possible store, the Y-intercept local. `collection` uses the existing array
separation in the opposite direction to retain every ordered hit record and
the cursor, with the same capacity reserve. No hit is appended or removed by
advancement, and the theorem does not grant extra capacity for a later scan.

`iteration` composes that invariant with the decoded grid-advance execution,
the numeric state, unchanged stack and natural iteration index. `counter`
handles endpoint exit before increment and the final iteration before budget
exit. `next_gate_iff` and `continuing_index` show that continuing supplies
`n+1 < 64` and the encoded next index, including stalled cells. These are
reusable end-of-cell facts, not premises about each reached loop state.

`E1M1FiringCollectionAdvance.execution` joins the retained collection with the
complete initialized first-cell state and the continuous post-sound firing
prefix. `next_cell` specializes the nonendpoint case: the real next-cell gate
has count one, the advanced numeric state and the same ordered production
scene-cell hits. The bound remains `427 + 281 * line_count + 230 * object_count`.
The previously supplied local-versus-heap contract already protects the store;
this connection adds no new memory or result assumption.

Still open: deriving next-cell lookup/scan inputs (including changed line
stamps), transporting the visited-line invariant across cells, and establishing
cumulative hit capacity. Then compose repeated cells with the actual source
loop and its early exits. Initial map/scene/list/geometry, successful arithmetic
and static layout assumptions still require reachable-state justification.
Aim clipping, damage and complete query/tic/observable correspondence remain
open. No runtime code or decoded instruction semantics changed.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringCollectionAdvance
python3 scripts/verify_e1m1_firing_collection_advance.py
python3 -m unittest discover -s tests -p test_e1m1_firing_collection_advance.py -v
```

The transitive certificate retains 29 authenticated DOS ranges and the 828-cell
map image. Negative tests cover missing/wrong store separation, an increased
capacity reserve, incorrect endpoint/budget ordering, missing observation or
collection premises, changed scene hits and an invalid unconditional next gate.


## Next-cell lookup and retained scan inputs

The one-tic obligation is still the path traversal inside the original firing
actions. `E1M1NextCellScan.inside` now executes the original grid step, caller,
signed bounds checks and BLOCKMAP lookup as one continuous prefix in the same
authenticated firing program. It starts at `0x2cab5` and reaches `0x2c57f`
within 49 instructions. The next coordinates are the numeric `step` result;
the selected raw cell list yields `ScanWords`. This applies to an arbitrary
continuing cell, including a stalled step, rather than only the first cell.
Endpoint and exhausted-budget paths are excluded by the explicit continuation
condition already characterized by `E1M1AdvanceCollection.next_gate_iff`.

`outside` joins the out-of-map branch within 43 instructions. It reaches the
thing gate `0x2ca9c` with restored caller SP and EAX = 1. This branch requires
no BLOCKMAP contents or assumed callback result. It does not execute the thing
iterator or skip its gate.

`E1M1NextCellMemory` frames the step's possible Y-intercept store together with
the next CALL/prologue stores. It transports dimensions, globals and the raw
map image from before advancement. The positive flag local is structurally
disjoint from the intercept store, so its enable byte needs no new layout
premise. The same epoch and possibly nonempty visited-line set survive, as do
the ordered hit records, exact cursor and unchanged reserve. Lookup itself
writes no memory. `scan_invariants` packages the retained mutable inputs.

The proofs reuse existing bounds/lookup execution; no bytes or instruction
semantics were changed. They do not reset visited bits between cells or infer
new capacity from the map's per-cell candidate bound.

**Remaining connection:** these are contracts from an arbitrary pre-advance
state. Derive their protected map/geometry reads, visited-set representation
and layout at the actual end of the earlier scans. Then connect next-cell
callback readiness and cumulative capacity. The first-cell firing theorem is
not yet extended through this next scan, nor is the outer production loop
proved by induction. Initial encoding/layout/freshness and successful
arithmetic obligations still need reachable-state discharge. Aim clipping,
damage, complete query/tic and audiovisual correspondence remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1NextCellScan
python3 scripts/verify_e1m1_next_cell_scan.py
python3 -m unittest discover -s tests -p test_e1m1_next_cell_scan.py -v
```

The certificate retains 29 authenticated DOS ranges and all 828 map cells.
Negative contract tests reject lost epoch/stamp protection, reset visited
history, missing map protection, fabricated capacity, old rather than advanced
coordinates, missing continuation/enable/selection conditions and wrong
control boundaries. Validation artifacts are in `artifacts/e1m1-next-cell-scan/`.



## Firing through the next-cell lookup

`E1M1FiringNextScan.execution` removes the pre-advance map/enable seam from the
previous generic next-cell proof. It joins the original post-sound firing entry
for either weapon through the complete first line/object cell, its numeric grid
advance and the next selected in-map BLOCKMAP lookup. The authenticated prefix
reaches line-list entry `0x2c57f`, with SP equal to original SP minus 124, within
`457 + 281 * first_line_count + 230 * first_object_count` modeled instructions.
The nonendpoint condition, next coordinates, raw list selection and in-map
condition remain explicit pure conditions on that next cell.

`E1M1FiringCellMemory.object_frame` generalizes the earlier local-only object
preservation to arbitrary protected words and handles empty object lists.
`firing_frame` composes it with initial setup and the complete line scan.
`after_lines_frame` deliberately starts after the line scan: it can carry
updated stamps, whereas preserving those from firing entry would be wrong.

`E1M1FiringMapState.map` derives dimensions, table/list/line pointers and the
raw BLOCKMAP image at the actual completed first cell from the original map
contract. Its added `Safe` contract contains only initial address separation
from line stamps, intercept records, stack stores and grid advancement.
It does not assume reached map values. `flag_word`/`enabled` prove the initialized
flag value and both traversal bits survive; their stack separation is proved
and heap separation comes from the existing flag contract.

The next lookup preserves the first scene cell's exact ordered hits/cursor.
`caller_array` obtains its three stack-slot protections from existing return
and first-scan layouts. No extra collection-layout or empty-hit premise is
introduced, and no capacity is manufactured: the conclusion retains reserve 0.

**Still open:** join the actual updated visited-set relation to this prefix,
derive next-cell callback geometry/readiness and cumulative capacity, then
induct over repeated cells and relate the outer production loop. This prefix
stops before the next line visitor; it is not the full first aim query or weapon
action. Reachable map/scene/list encodings, freshness, successful arithmetic,
static layout, aim clipping, damage and complete tic/observable correspondence
remain obligations. No runtime or instruction-semantics code changed.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextScan
python3 scripts/verify_e1m1_firing_next_scan.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_scan.py -v
```

The strict transitive certificate retains 29 authenticated DOS ranges and 828
map cells. Contract tests reject missing first/object scan protection, treating
updated memory as initial memory, missing flag/map separation, wrong next-cell
selection, missing continuation and fabricated capacity. Validation artifacts
are in `artifacts/e1m1-firing-next-scan/`.



## Visited history at the next cell

`OriginalLineVisitedRun` reuses the existing stamp-update and mixed-scan
invariants to prove visited-set correspondence for the continuing scan used by
aiming. Its `finished_represents` reaches the same sentinel-return model used
by the firing theorem. Marking preserves array size and already-set bits; a
valid first candidate is marked even if its geometry produces no intercept.

`E1M1FiringLineVisits.visit_layout` derives mutable stamp protection from the
existing first-scan layout plus explicit stamp side/scratch/metadata separation.
`scan_seen` starts from an arbitrary bitset represented at the incremented epoch
before firing code runs. `fresh_scan` specializes to 475 false bits using
explicit freshness against that incremented epoch. Freshness is not inferred
from wrapping counter arithmetic. The resulting `seenAfter` marks the original
candidate order, including repeated IDs and the leading linedef zero.

`E1M1FiringVisitedNext.before_seen` carries this derived relation through object
lookup, the complete object list and caller return. Its `TailSafe` contract only
protects stamps from subsequent writes; requiring a stamp to be disjoint from
its own earlier line-scan write would make the contract unusable. `next_seen`
then transports the same epoch and bitset through grid advancement and lookup.
All added safety premises describe initial addresses, not reached stamp values.

`execution` joins the visited relation with the existing continuous prefix,
selected next line list and retained hits at the same reached state. The bound
remains `457 + 281 * first_line_count + 230 * first_object_count`. `seen_zero`
and `leading_duplicate` additionally establish the actual next cell's initial
duplicate condition: its mandatory linedef-zero entry has already been marked.
This branch fact needs no intersection computation or free hit slot. The
instructions that skip this entry are not yet part of the joined prefix.

**Remaining work:** connect next-cell callback readiness, consume duplicate
branches, derive cumulative capacity and induct over repeated cells with the
actual source loop. Source initialization uses the fixed 475-line profile;
the complete loop equivalence is not established by the local bitset relation.
Initial memory/scene encodings, layout, freshness and successful arithmetic
still require reachable-state discharge. Aim clipping, damage, full query/tic
and audiovisual correspondence remain open. The theorem preserves reserve 0,
not capacity for the next append. Runtime and instruction semantics are unchanged.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringVisitedNext
python3 scripts/verify_e1m1_firing_visited_next.py
python3 -m unittest discover -s tests -p test_e1m1_firing_visited_next.py -v
```

The strict transitive certificate retains 29 authenticated DOS ranges and 828
map cells. Contract tests reject lost history, wrong initial epoch, missing
freshness/layout, incorrect stack rebasing, an unmarked duplicate claim and
fabricated hit capacity. Artifacts are in `artifacts/e1m1-firing-visited-next/`.


## Duplicate skip and remaining capacity

`E1M1DuplicateSuffix.skip` executes the original duplicate branch in the same
program/code-memory model as the firing prefix. The already-proved next-cell
leading-zero condition supplies its branch premise. Within ten instructions,
the cursor advances by one 16-bit entry and control returns to the scan header;
all memory and the stack pointer are unchanged. `scan_tail` transports each
remaining ID/pointer and the sentinel to that advanced cursor. The tail descriptor
is deliberately not claimed to satisfy the fresh BLOCKMAP-list validity contract.

`E1M1CellCapacity.collect_bound` proves that a successful production object-list
scan adds at most one hit per candidate, including rejected intersections and
empty lists. `scene_bound` applies it to the actual selected scene cell in the
same object-ID order. Combined with the existing first line-scan bound, the
joined result has at most `first_line_count + first_object_count` hits. The
existing first-cell budget therefore supplies conservative reserve
`128 - (first_line_count + first_object_count)`. `suffix_reserve` can supply
remaining-candidate capacity when their count plus that first-cell bound is at
most 128. It does not infer traversal-wide capacity from reserve zero.

`E1M1FiringNextSuffix.execution` joins those results to the continuous prefix
starting at the common post-sound firing state. Its bound is
`467 + 281 * first_line_count + 230 * first_object_count`. At the same reached
state it retains exact suffix metadata, the original ordered intercept array,
the updated visited relation, the stack position, and the derived reserve.
No new assumptions about reached stamp values or reached hit counts are added.
The underlying initial contracts and first-cell continuation premises remain.

**Remaining work:** transport callback readiness to the remaining next-cell
candidates, join their execution, and establish a capacity invariant that can
support repeated-cell induction and the actual production outer loop. The
current two-cell budget is sufficient but has not been established for every
reachable traversal. Initial memory/scene encodings, arithmetic, freshness and
layout still need reachable-state discharge. Aim clipping, damage, complete
query/tic and audiovisual correspondence remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextSuffix
python3 scripts/verify_e1m1_firing_next_suffix.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_suffix.py -v
```

The certificate retains 29 authenticated DOS byte ranges and 828 map cells.
Contract tests reject incorrect branch/entry premises, a stationary cursor,
substitution of the full list for its tail, missing scene correspondence, and
unjustified reserve. Artifacts are in `artifacts/e1m1-firing-next-suffix/`.
Runtime and instruction semantics are unchanged.


## Next-cell callback readiness

`E1M1NextCallbackMemory` transports immutable words through the completed first
cell, grid advance and next lookup. Its separate `initialized_frame` starts
from the initialized first scan, so trace coordinates and the active flag are
not incorrectly equated with old firing-entry globals. `line_words` retains
both vertices, deltas and the production wrapping endpoint sums. The callback
address is derived from the actual caller and iterator prologue stores.

`E1M1NextCallbackReady.Data` describes line data at the original firing boundary,
address separation for its lifetime, and successful production fractions for
crossings. Its indices refer to the exact remaining list after the leading
duplicate. `Ready` describes indexed callback templates at the reached suffix:
geometry, back-sector tests, active flag, callback address and storage layout.
`rejection` and `crossing` convert these into the existing original callback
contracts, using the actual side decision. They do not assume reached side
registers or computed fraction values.

`E1M1FiringNextGeometry.execution` joins readiness to the continuous firing
prefix and retains the exact suffix, ordered collection, conservative reserve
and updated visited relation. Initial line values are framed across the first
scans; initialized trace/flag values are framed from their real writes. The
storage layout is reused from the original firing contract. The instruction
bound remains `467 + 281 * first_line_count + 230 * first_object_count`.

**Remaining work:** assemble these indexed templates into the scan invariant
and execute the remaining next-cell candidates. The resolver must preserve the
mixed line/object collection already accumulated in the first cell. Capacity
for the suffix needs a sufficient candidate budget; the general repeated-cell
capacity invariant remains open. Then join repeated cells to the production
outer loop. Initial encodings, arithmetic, separation and freshness still need
reachable-state discharge. Aim clipping, damage and full query/tic remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextGeometry
python3 scripts/verify_e1m1_firing_next_geometry.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_geometry.py -v
```

The strict certificate retains the same 29 authenticated DOS ranges and 828
map cells. Tests reject wrong callback addresses/stack positions, missing
lifetime protection, substitution of old globals for initialized values,
incorrect branch decisions, and readiness claimed for the wrong list.
Artifacts are in `artifacts/e1m1-firing-next-geometry/`. Runtime and instruction
semantics are unchanged; no extra callback execution is claimed by this join.


## Next-cell line execution

`E1M1NextCursor.firing_cursor` derives the next line-list address from the actual
grid step, preserved BLOCKMAP image and selected offset. `tail_address` carries
that modular address across the leading duplicate skip, and `tail_ids` derives
the suffix ID bound from the original list validity.

`E1M1NextLineScan.initial` assembles the existing scan invariant from the reached
callback readiness and static suffix layout. It uses the mixed line/object
resolver from the completed first cell; changing the resolver does not change
the candidate geometry, storage or mutable-stamp layout. No all-lines condition
is imposed on the incoming hit array. `step_prefix` and `run_prefix` establish
that existing records stay in order across every branch and that new hits can
only be appended.

`E1M1NextLineScan.execution` reuses the existing continuing-scan and visited-set
proofs to execute every suffix candidate and the sentinel return. Its output
contains the encoded mixed collection, updated visit history and protected-word
frame. `E1M1FiringNextLines.execution` joins that execution to the continuous
post-sound firing prefix. Its instruction bound is
`474 + 281 * (first_line_count + next_tail_count) + 230 * first_object_count`.
The actual first-cell scene result supplies the incoming hits. Their order is
preserved as an exact prefix of the final list.

The added initial requirements are static layout for the suffix at its derived
address and the conservative budget
`first_line_count + first_object_count + next_tail_count ≤ 128`. The budget
supplies capacity via the previous first-cell size bound; no new assumption is
made about the reached hit count. This bound is sufficient and has not been
proved for every reachable multi-cell query.

**Remaining work:** derive the restored caller observations at this sentinel
return and join its success test, then execute the next cell's object list.
Establish repeated-cell capacity and induction, and connect the production
outer loop. Initial encoding, arithmetic, separation and freshness contracts
still require reachable-state discharge. Aim clipping, damage and full
query/tic remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextLines
python3 scripts/verify_e1m1_firing_next_lines.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_lines.py -v
```

The strict certificate retains the same 29 authenticated DOS ranges and 828
map cells. Contract tests reject wrong cursor/selection, missing callback
readiness or layout, zero reserve substituted for a candidate budget, lost
history, reordered old hits, and underestimated instruction bounds. Artifacts
are in `artifacts/e1m1-firing-next-lines/`. Runtime and instruction semantics
are unchanged.


## Next object-iterator entry

`E1M1NextLineReturn` extends the existing mixed scan invariant with protected
words without changing its execution. It preserves arbitrary additional reads,
then specializes to the saved EDI/return address and the initialized enable word.
The resulting `parent_return` proves success, restored SP and EDI, and the PC
loaded from the actual saved return word. It reuses the original `ReturnSafe`
and `FlagSafe` contracts at the same firing stack position.

`E1M1NextSavedFrame.saved_words` derives that next saved EDI and return word
from the actual caller/prologue. `flag_word` carries the initialized options
through the first object scan, grid advance and next lookup. Combined with the
memory-preserving duplicate skip, these supply the inputs to the second line
iterator's restoration proof; no reached saved-word values are assumed.

`E1M1FiringNextThings.enter` executes the line-success test, object-enable gate
and real CALL. The output enters `P_BlockThingsIterator` at `0x2c5a0`, with
callback `0x2c720` and return word `0x2cab1`. The callee SP is firing SP minus 116, and the
argument registers come from the actual retained ESI/ECX. The CALL's single store retains mixed
intercepts and the incremented epoch/visited stamps under the existing address
protections. The helper is reusable at later line-return boundaries.

`execution` joins this segment to the continuous post-sound firing prefix,
with bound `482 + 281 * (first_line_count + next_tail_count) +
230 * first_object_count`. It retains the exact earlier-record order and updated
visited relation. No additional semantic or reached-state premise is introduced;
existing initial contracts and the sufficient two-cell candidate budget remain.

**Remaining work:** identify retained ESI/ECX with the intended next-cell
coordinates, execute its object-table lookup, derive list/callback readiness
and run the list. This join stops at iterator entry and does not assume the
coordinate identification. Repeated-cell capacity/induction and the production
outer-loop connection remain open, as do initial reachable-state discharge,
aim clipping, damage and the complete query/tic.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextThings
python3 scripts/verify_e1m1_firing_next_things.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_things.py -v
```

The strict certificate retains 29 authenticated DOS ranges and 828 map cells.
Tests reject wrong saved offsets, missing return/flag separation, a disabled or
unsuccessful caller, lost hit/stamp protection, wrong callback/return addresses
and underestimated instruction bounds. Artifacts are in
`artifacts/e1m1-firing-next-things/`. Runtime and instruction semantics are unchanged.


## Next-cell object lookup

`E1M1NextCoordinates` reuses the generic coordinate-restoration theorem for the
mixed line scan. The actual grid-step observation supplies the next X/Y values;
the caller lookup and duplicate skip preserve them. No reached-coordinate
premise is added. Existing record/stack separation protects both coordinate
spill slots across every remaining line callback.

`E1M1NextThingLookup.execution` reuses the authenticated object-iterator entry,
signed bounds and table-index arithmetic. For an in-map cell it identifies the
loaded head, then covers both outcomes: an empty list returns success to
`0x2cab1` at firing SP minus 112; a nonempty list reaches `0x2c5d2` with that
head in EDX and the saved `0x2c720` callback at firing SP minus 120. The prologue
store preserves the mixed intercepts, cursor, epoch and visited history.

`E1M1FiringNextLookup.execution` joins this to the same continuous post-sound
prefix, with bound `502 + 281 * (first_line_count + next_tail_count) +
230 * first_object_count`. It derives the iterator's actual coordinates and
all lookup reads. Width/height come from the original map contract; the table
pointer and selected head come from initial firing memory. Existing frame
lemmas transport those words through the first cell, grid step, second line
scan and CALL. New assumptions are the initial selected head and address
protections for those two table reads, not post-call correctness assumptions.

This advances the firing action's ordered-intercept-collection obligation.
**Remaining work:** derive the second object's trace/geometry/list readiness
and sufficient capacity, then reuse object-list traversal. The head still needs
to be tied to the production scene's ordered node list. Initial memory contracts,
fractions, layout and freshness remain explicit; repeated-cell capacity and
induction, the production outer loop, aim clipping, damage and full query/tic
correspondence remain open. The theorem is not complete aiming or firing parity.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextLookup
python3 scripts/verify_e1m1_firing_next_lookup.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_lookup.py -v
```

The strict certificate retains 29 authenticated DOS ranges and 828 map cells.
Tests reject missing coordinate, head-value or memory-separation premises,
wrong empty/nonempty destinations and stack positions, changed head pointers,
lost hit/stamp protection and underestimated continuous bounds. Artifacts are in
`artifacts/e1m1-firing-next-lookup/`. Runtime and instruction semantics are unchanged.


## Complete second object scan

`E1M1NextObjectMemory` supplies a reusable read-preservation theorem from a
mixed line scan through its return, object CALL and object-table lookup. It
works for immutable object data and initialized trace words alike. The saved
caller word is derived from the CALL/prologue, not supplied as an image premise.
The generic mixed-scan size bound retains the incoming count and adds at most
one record per remaining line candidate.

`E1M1FiringNextObjectImage.execution` derives the second finite node chain's
memory image and layout at the reached lookup boundary. Object X/Y, radius and
links come from initial firing memory; trace words come from setup. The saved
callback is supplied by the actual iterator prologue. A sufficient initial
budget covering first-cell lines/objects and second-cell remaining lines/objects
establishes space for the entire next list before it executes. No reached
geometry, link image, callback success or output capacity is assumed.

`E1M1NextObjectTraversal.execution` reuses the existing finite-list induction
on arbitrary mixed incoming hits. Empty lists have already returned from lookup;
nonempty lists execute their callbacks, next-link decisions and real epilogue.
Both cases return success at the original caller site and preserve visited
history under the existing object-write separation. This wrapper is reusable
at later cell lookup boundaries.

`E1M1FiringNextObjects.execution` joins the traversal to the continuous firing
prefix, with bound `505 + 281 * (first_line_count + next_tail_count) +
230 * (first_object_count + next_object_count)`. The result is success at
`0x2cab1`, firing SP minus 112, with the final mixed intercept collection equal
to the selected next production scene cell's object-collection result. The
scene's ordered ID array is tied to the exact finite DOS node chain. The updated
visited stamps survive every object callback.

This completes another part of the firing action's intercept-collection
obligation, not the entire aim query. **Remaining work:** preserve and assemble
the full cell-boundary invariant (grid locals, map/list data, mixed hits and
visited state), then lift it to repeated-cell execution and the production outer
loop with the 64-iteration cap and early exits. The explicit sufficient candidate
budget is not a proof of capacity for every reachable trace. Initial data,
fractions, layout, freshness and dynamic scene/list relations still require
reachable-state discharge. Ordered intercept processing, aim clipping, query
returns/retries, damage and whole-tic correspondence remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextObjects
python3 scripts/verify_e1m1_firing_next_objects.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_objects.py -v
```

The strict certificate retains 29 authenticated DOS ranges and 828 map cells.
Tests reject lost incoming hit counts, wrong saved caller slots, missing initial
object/link data or read protection, insufficient capacity, lost visited history,
unrelated scene cells and incorrect instruction bounds or caller returns.
Artifacts are in `artifacts/e1m1-firing-next-objects/`. Runtime and instruction
semantics are unchanged; no emulator rerun is claimed.


## Reusable object-to-grid boundary

`E1M1ObjectBoundary.preserved` combines the existing object register and frame
lemmas for empty and nonempty lists. It preserves ECX, EBP, ESI and EDI, every
protected memory word, and restores the caller stack. `observe` packages this
as preservation of all eleven numeric grid fields. `callerView` merely reads
those fields at the caller's SP rather than the iterator's temporary stack
position; it is an observation, not an extra executed operation.

`E1M1CellBoundaryAdvance.Returned` packages successful return PC/value, stack,
numeric observation, mixed hits and visited history. It deliberately does not
claim to contain all next-cell map/list or capacity obligations. `execution`
joins the real caller TEST/JZ and numeric step in at most 21 instructions, with
output equal to the original `step` and PC equal to `nextPc`. Existing numeric
lemmas interpret that PC as endpoint/budget behavior for legal counters. Ordered
records, cursor and visited state survive the step's possible Y-intercept store.
The separate read-frame lemma supports later map/node contract preservation.

`E1M1FiringNextBoundary.execution` applies those reusable proofs to the actual
second object scan and its already derived image/capacity. The continuous bound
is `526 + 281 * (first_line_count + next_tail_count) +
230 * (first_object_count + next_object_count)`. Its collection still matches
the selected production scene cell, and visits/protected reads survive through
advancement. No additional reached-state premise is introduced.

**Important remaining identification:** the numeric input to this step is the
actual second lookup state viewed at caller SP. It has not yet been identified
with the complete production-initialized first advance across the preceding
line scan and lookup. The first cell already has initialized numeric
correspondence; this new theorem supplies the reusable preservation and control
transition after the second object lookup. It is not yet a closed iteration
invariant or a proof that every later cell has sufficient intercept capacity.

Next bridge that numeric observation, preserve/assemble the remaining map/list
contracts at the same boundary, and prove repeated-cell execution with the
original cap and exits. Initial encodings, successful fractions, layout,
freshness, sufficient candidate budget and dynamic scene/list relations remain
explicit. The production outer loop, ordered intercept processing, aim clipping,
query returns/retries, damage and whole-tic correspondence remain open.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextBoundary
python3 scripts/verify_e1m1_firing_next_boundary.py
python3 -m unittest discover -s tests -p test_e1m1_firing_next_boundary.py -v
```

Tests reject wrong caller stack views, missing list/capacity or local protection,
missing epoch/stamp separation, unconditional continuation instead of original
control, lost read protection and underestimated instruction bounds. The strict
certificate retains the same 29 DOS ranges and 828 map cells. Artifacts are in
`artifacts/e1m1-firing-next-boundary/`. Runtime and instruction semantics are
unchanged; no emulator rerun is claimed.


## Finite successive-hit induction and exits

The successive-hit induction from aiming work package 1 is now established for
the currently covered open-two-sided-line branch. The next branch work is package
2: connect one-sided walls and closed openings to the same iteration framework.
The full mixed line/actor loop remains package 4 after those cases are available.

- `E1M1AimPortalPrefix.Position` holds the source work buffer, clipping bounds
  and portal log. `Sequence` certifies any finite continuing prefix using only
  the actual strict-min selections, catalog membership, open-sector comparisons,
  guarded divisions and updated-window comparisons. It contains no machine
  transitions, intermediate machine invariants or assumed callback outputs.
- `seed` constructs the reusable boundary from the actual first selected callback
  and its initial persistent invariant, normalizing the real parent stack word.
- `execution` inducts over `Sequence`. At each iteration it derives the next
  selected callback from the preceding aligned boundary, executes the authentic
  synchronized cycle, and passes the resulting history, invariant and bounds to
  the induction hypothesis. It concatenates actual original instruction prefixes
  into one trace bounded by `count * (157 + 7 * initial.size)`. The production
  source suffix equality composes over the exact chronological indices. The final
  boundary retains either a traversal exit or a reusable next callback.
- The consumed history grows by exactly `count`; `capacity` derives
  `count <= initial.size - seen.length` from distinct-record traversal. This
  prevents an arbitrarily long continuing prefix within a fixed vanilla buffer.
- `E1M1AimPortalPrefixExit.terminal` retains the real normal exit PC, including
  the historical ESI wrap on exhaustion. `completed` combines that exit and the
  source no-target suffix result with the whole prefix.
- `stopped` executes a further callback whose sector gap is open but whose clipping
  closes the accumulated window. It joins the whole instruction trace, retains
  the actual 0x2c88c stop boundary and final clipping bounds, and proves the source
  result truncates at `seen.length + count + 1`. The last visit is not counted as
  another consumed prefix record.

These are conditional prefix and end-case theorems, not a claim that every query
has only portal hits. Source branch coverage still must produce the appropriate
sequence/case evidence. Other line outcomes and actors need their corresponding
cycle contracts before the entire mixed-hit loop can be closed. Initial map,
query, memory and source/catalog relations remain entry interfaces; reachable
E1M1 states must establish them and the conditional division obligations. Outer
query return and three-probe controller composition remain separate.

Evidence: `artifacts/e1m1-aim-portal-prefix/validation.json`. The inherited strict
certificate covers the same 42 binary ranges and 828 map cells. Mutation checks
reject missing source sequences/initial boundaries, incorrect instruction bounds,
lost consumed counts, stale final bounds/suffixes, missing normal exit conditions
and off-by-one stopping visits. A kernel-checked two-portal tied-distance example
constructs a valid sequence; reusing the first index or continuing with a closed
window is rejected. Prior synchronized-cycle tests are rerun. No runtime, decoder,
instruction semantics or earlier Doom proof source changes; binary diagnostics
are inherited evidence and were not rerun.

## Synchronized source and DOS portal cycle

The persistent binary callback transition and the precomputed source path are
now joined in one theorem, with their common scene representation explicit.

- `E1M1AimSourceCatalog.Represents` relates every listed original intercept to
  source front/back heights and two-sided flags. It is partial: an unlisted hit
  is not classified. `entry` transports the immutable representation to the
  actual selected work record. `arithmetic` converts signed opening bounds,
  guarded floor/ceiling divisions and updated window values to the existing DOS
  callback contract; no equality of callback outputs is assumed.
- `E1M1AimSynchronizedCycle.indices` exposes the next index of the canonical
  remaining `List.range'`, retaining its exact length. `boundary` combines the
  original traversal's exit/next-call result with source path ordering: terminal
  boundaries have an empty source suffix, while a reached callback has its
  persistent invariant and exact chronological source hit.
- `execution` derives source map facts and the selected hit, executes the real
  callback/return/mark/rescan/CALL sequence within `157 + 7 * work.size`
  instructions, and advances the production source suffix. It proves identical
  lower/upper clipping bounds and the same continue/stop decision. On continuing,
  the consumed history and aligned next boundary are returned together. A
  stopped callback retains its original stop PC and the source's exact truncated
  visit count. The complete machine frame is retained.
- `next_callback` uses an admitted next minimum to rule out terminal boundaries.
  It recovers the exact next fraction/index and persistent machine invariant;
  neither a new entry invariant nor a guessed source hit is supplied.

This closes the single-cycle composition seam, not repeated-loop induction.
The shared initial collection, empty initial visits, successful production
visitor result, source/catalog representation and initial persistent state are
still interfaces to discharge from query entry. Each proved cycle requires its
selected catalog entry, open sector interval and successful height-dependent
divisions. Other callback branches, the full loop and outer query return still
need their correspondence proofs. No whole-game claim follows.

Evidence: `artifacts/e1m1-aim-synchronized-cycle/validation.json`. The inherited
certificate retains the 42 original code ranges and 828 map cells. Mutations
check the source/catalog relation, signed clipping, conditional guards, exact
remaining indices, terminal-vs-next boundary, actual callback stack, consumed
record and source stop count. An empty source catalog remains valid, making
partial classification explicit. Prior path-order and production-visitor edge
cases are rerun. The original-binary diagnostic is inherited, not rerun. Runtime,
decoder, instruction semantics and all prior Doom proof sources are unchanged.

## Precomputed aim-path order and source suffix

The repeated DOS selection history is now tied to the exact all-hit visitor
that supplies the source aiming loop's precomputed path.

- `E1M1AimPathOrder.replay` inducts over `History` to reconstruct the production
  walk at the corresponding remaining budget and appended log. The strict-min
  scan, sentinel marking and tie order remain the existing production operations.
- `suffix` proves that subsequent all-accepting iterations only append records.
  `next_hit` combines it with replay to derive both bounds and exact hit identity
  at the chronological index, including a nonempty prior visit log.
- `terminal` handles both complete consumption and an out-of-range minimum. It
  proves that the entire output log is precisely the prior log plus this history,
  so neither termination case can leave an unprocessed source hit.
- `E1M1AimPathBridge.selected` uses the actual reached DOS `Selection` to derive
  the next source hit and its equality to the original unmarked record. The
  production open-two-sided-line step `next_line` now obtains its hit identity
  from that result. `finished` proves the production source suffix returns its
  path without a target when the history reaches either normal traversal exit.

These theorems assume the same initial collection, successful production
`visitHits` output and (for the aim bridge) empty initial visits. They do not
assume that every hit is a portal or that every callback continues. The source
line step still needs its branch and conditional division premises. Full loop
induction must join collection/query entry, these source suffix facts and the
persistent machine transition; initial invariant and other callback cases remain
open. No complete aiming, rendering, audio or whole-game claim follows yet.

Evidence: `artifacts/e1m1-aim-path-bridge/validation.json`. The strict inherited
certificate covers the same 42 original byte ranges and 828 map cells, plus the
new general theorems and three checked bridge contracts. Mutation checks reject
lost history, wrong callback index, missing range rejection, shifted original
records, discarded prior logs and altered source stop counts. Executable visitor
cases cover empty/all-far inputs, tied distances, 65536/65537 boundaries, negative
and extreme signed fractions, mixed record kinds and the 128-record buffer.
The prior binary diagnostic is inherited, not rerun. Engine behavior, decoder,
instruction semantics and every prior Doom proof source remain unchanged.

## Persistent catalog and reusable callback invariant

The local next-line conditions are now assembled into a persistent invariant
that the actual open-line callback cycle reconstructs at its next callback.

- `E1M1AimCatalog` indexes immutable portal descriptors by original intercept
  index. Its partial catalog represents two-sided lines without claiming all
  hits belong to that branch or that all represented sectors have an open gap.
  `preserved` transports every catalog entry simultaneously using the one cycle
  frame and unchanged stack. `inputs` instantiates the actual selected entry
  and derives mapped callback, fraction/range and clipping-read conditions.
- `E1M1AimTraversalInvariant.Persistent` combines the catalog, buffer layout,
  query protection and values, fixed clip-global protection, capacity, callback
  function slot, slot/record separation, and fraction-independent resolution
  for the initial records. The evolving window is returned separately.
- `preserved` derives the whole next invariant from the existing selected-entry,
  map, query and stack proofs. It also proves the real callback slot survives,
  so the next selected callback has address 0x2b760. `carried` leaves exhaustion
  and range rejection explicit and strengthens the callback outcome.
- `execution` derives the current callback's entry premises from the invariant
  and catalog, executes the authentic clipping/return/mark/full-rescan/CALL
  sequence within `157 + 7 * work.size` instructions, and returns the invariant
  with the next selected hit. The stopped callback branch remains unmarked;
  both paths retain the computed clipping bounds. No next-state invariant or
  callback result is supplied as a premise.

The invariant still must be established from the actual initialized query/map
and resolver, rather than assumed for the whole game. A cycle requires the
selected catalog entry, an open two-sided sector interval and successful
conditional divisions. The catalog permits unclassified hits; this theorem does
not silently discard them or prove their callbacks. Next is the repeated-loop
argument and precomputed source aim-suffix alignment, with other callback
branches and reachable-state obligations still open.

Evidence: `artifacts/e1m1-aim-traversal-invariant/validation.json`. The inherited
certificate authenticates the same 42 original code ranges and 828 map cells.
New contract mutations cover the catalog index, actual cycle frame, mark pointer,
callback slot, changed window, consumed history and stopped exit. An empty-catalog
check confirms that no universal line classification is built into the definition.
The existing map-byte/clipping diagnostic was rerun for 384 original traversals
and 3,410 callbacks; it is reused diagnostic coverage. All prior Doom sources,
engine behavior, decoder and instruction semantics are unchanged.

## Persistent map image and next mapped-line inputs

The next callback's map inputs are now derived from the preceding state and the
full-cycle frame, including the smaller fields actually read by the binary.

- `E1M1AimMapFrame.StableWord` requires callback-write separation, separation
  from all 128 possible intercept-fraction slots, the cursor store and the next
  CALL return word. `Region` applies it to the flags word and all opening-map
  reads. Both conditions transfer under the proved identical callback stack.
- `word`, `byte` and `half` preserve exact 32-, 8- and 16-bit observations.
  `image` transports the two sector pointers, four heights, halfword side index
  and exact flags byte for a line that can differ from the just-processed line.
- `opening_safe` and `floor_safe` derive read protection for the helper/clip
  subprograms from the established full callback protection. `map_safe` provides
  the next opening helper's map-read condition.
- `E1M1AimNextLine.entry` combines that image with the actual reached selection,
  original hit record, stack/layout and query invariants. It constructs the next
  `E1M1AimMapped.Inputs`, `E1M1AimDistance.ReadSafe`, and
  `E1M1AimCeilingEntry.ClipSafe`, and returns persistent region/global separation.
  The next line's flags, record, sector image and protection conditions are not
  replacement-state premises. Its line kind, two-sided bit, map image and region
  protection are still required in the preceding state.

The fixed globals used after floor clipping are handled by `ClipGlobalsSafe`,
which depends only on stack layout. This avoids incorrectly asserting that the
opening helper's output globals or the evolving clipping window stay unchanged.
All arithmetic and memory reasoning remains in the existing bit-vector semantics,
including unaligned map fields and wrapping stack addresses.

Next: collect these per-line facts into a persistent invariant for whichever hit
is selected, and compose it with the full callback-loop induction and precomputed
source aim-suffix alignment. Other callback branches, division obligations,
reachable-state establishment and the final observable-tic theorem remain open.

Evidence: `artifacts/e1m1-aim-next-line/validation.json`. The inherited strict audit
still authenticates 42 original code ranges and 828 pinned map cells. The emulator
diagnostic extends the preceding cycle diagnostic with varied flags, nonzero
side indices, initialized padding and exact snapshots of the entire 128-byte
map allocation for each record, checked at every callback and final exit.
Its 384 uninterrupted traversals contain 3,410 callbacks. This is diagnostic
coverage, not the universal loop theorem. All prior Doom proof sources, engine
code, decoder and instruction semantics are unchanged.

## Clipping cycle and reusable next-entry invariants

The stronger history-aware dispatch is now composed with the existing callback
execution, rather than left as a separate next-search theorem.

- `E1M1AimHistoryCycle.next` uses the established selection contract to derive
  the consumed buffer, pointer, cursor, counter and maximum at the actual parent
  resume state. It joins directly to `E1M1HistoryDispatch.execution`.
- `carried` transports the original indirect callback slot and parent stack to
  the next outcome, using the callback/mark read frame.
- `execution` runs continuously from callback entry through the real open-line
  clipping code, return, parent stop/mark and next selection within
  `157 + 7 * hits.size` instructions. A continuing window advances source
  history; a closed window reaches the original callback-stop exit. Both retain
  the computed floor/ceiling bounds. The additional `Frame` covers protected
  words throughout the callback, mark, cursor store and next CALL.
- `E1M1AimCycleInvariant.stack` derives identical callback-entry ESP for the next
  hit. `layout` uses that equality to transfer eleven fixed layout conditions,
  including record, return-slot, cursor, query-read and callback-slot separation.
  The `record` theorem reads the explicit next selected original hit from actual
  callback memory. `query_words` preserves range and eye height, while
  `query_safe` proves that the next bounded record remains disjoint from those
  globals. `entry` assembles these consequences without assuming next-state
  layout or query data.

These are conditional local theorems for an open two-sided line. The next map
image, byte-level flags and line-specific pointer/separation contracts still need
to be transported. The source's precomputed all-hit aiming suffix is not yet
identified with the complete repeated selection sequence. Other callback
branches and the full machine-loop induction, reachable-state discharge and
observable-tic theorem remain open. The earlier source visitor induction and
continuous clipping proofs are reused unchanged.

Evidence: `artifacts/e1m1-aim-history-cycle/validation.json`. The strict transitive
certificate authenticates the same 42 DOS code ranges and 828 map cells. The new
emulator diagnostic executes 384 uninterrupted original traversals with distinct
portal heights per record, checking every callback's buffer/order/counter,
clipped window, query words, cursor, return word and stack. It covers 3,410
callbacks, 171 multi-callback runs and 89 runs with more than one changed window.
This is diagnostic evidence, not a substitute for loop induction. Runtime,
decoder, instruction semantics and all prior Doom proof sources are unchanged.

## Repeated callback entry and source history

The repeat-head budget now reaches the callback through the actual minimum scan
and indirect CALL, under the existing unified decoded program.

- `E1M1SelectionRegisters.scan` and `.execution` retain ESI as well as the maximum
  distance and stack. Their induction covers both strict-min branches and the
  full initialized scan; earlier theorem interfaces remain unchanged.
- `E1M1NextCallbackState.dispatch` establishes the full callback buffer, actual
  destination, pushed return word, EAX/EBX alias, saved end cursor, unchanged ESI,
  and EDI maximum. Protected reads survive; `callback_slot` derives preservation
  of the function pointer even across a wrapping stack. Cursor/record separation
  remains an explicit premise, not a universal claim about arbitrary memory.
- `E1M1HistoryDispatch.execution` starts at the real repeat head and reaches
  exhaustion, range rejection, or the next callback within `13 + 7 * work.size`
  instructions. From the source history it derives that the selected index is
  fresh, the record is still the initial original record, and ESI encodes
  `initial.size - (j :: seen).length`. Exhaustion preserves DOS's decrement from
  zero to MAXUINT.
- `source_continue` and `source_stop` connect that selection to the extracted
  production visitor's next step, using `priorVisits.size + seen.length` for the
  callback index. Continuation advances source history and fuel; stopping logs
  the rejected hit without claiming a machine sentinel store.

The new entry theorem is a local conditional theorem for a buffer of at most
128 records, a valid history, encoded memory, the correct counter/cursor/maximum,
and separated traversal stores. It is not a complete callback-loop theorem.
Next: compose these stronger entry facts with callback execution and prove the
remaining map/global/stack invariant and precomputed aiming-suffix alignment.
Other line branches, actor targeting, reachable-state discharge and the final
observable-tic theorem remain open.

Evidence: `artifacts/e1m1-history-dispatch/validation.json`, its strict inherited
certificate/axiom audit, new mutation tests and ordered-history regressions.
The existing authentic repeated-traversal emulator diagnostic is reused rather
than counted as a second independent model. No prior Doom source, runtime,
decoder or instruction semantics changed in this batch.

## Ordered-history induction and traversal budget

`E1M1OrderedVisit` extracts the exact production visitor, including its mutable
work buffer and early callback return, into an exposed iteration and a structurally
recursive `walk`. The proof connects it to `E1M1QuerySource.visitHits`, which is
already connected to production `Scene.pathTraverse`. It preserves the original
strict minimum scan, inclusive signed range cutoff, callback index, append-before-
callback ordering, continuation mark and iteration count. This is proof-only
extraction; no runtime sorting or traversal is replaced.

`E1M1SelectionHistory` tracks admitted selections using the actual minimum
function. Its image theorem establishes that selected fractions are MAXINT while
all untouched records remain original. The selected-value lemma then proves an
admitted next index cannot already have been consumed. History indices are in
bounds and distinct; visit counts equal selection counts; the log contains the
original records in selection order. `same_count` proves two histories of the
same collection coincide after the same number of selections, including tied
fractions. A terminating callback's last mark may be logical bookkeeping only;
these source history theorems do not assert that DOS wrote it.

`E1M1OrderedTraversal.traversal` performs the full fuel induction, handling range
exit, missing-choice impossibility, continuing callbacks and stopping callbacks.
Its `live_history` corollary quantifies over arbitrary finite input collections
and arbitrary Boolean callbacks and proves successful source return with the
history, original-record log, no duplicate indices, visit bound and unchanged
collected array. Initial visit logs are retained and callback indices include
their length.

`E1M1TraversalBudget` bounds history length by the original capacity, relates each
admitted selection to one fewer remaining iteration, and applies this arithmetic
to the original four-instruction repeat head. For the supported 128-record buffer,
no unintended counter wrap is possible while work remains; exhaustion retains
the original decrement-to-MAXUINT behavior. `resumed_budget` obtains the preserved
counter from the completed callback and parent rather than assuming a different
post-call value.

Remaining: machine-loop induction with scan-to-next-callback counter preservation
and all callback entry images/separation; matching the source history to the
precomputed all-hit path suffix; unified line branches, actor targeting and
reachable-state discharge. The new source induction does not discharge those
machine obligations or prove whole aiming/game equivalence.

Validation: `artifacts/e1m1-ordered-history/validation.json`. Strict transitive
axiom audit; proof-contract mutations; concrete live-source tests for signed
fractions, ties, cutoff, early stop and initial visit offsets. Independent x86
diagnostics cover 256 complete traversals and 5,553 authentic line callbacks,
checking each callback's selected index, remaining counter and return frame,
then the full final buffer and exit. No callbacks are substituted. These cases
use equal-height sectors to isolate ordering; earlier checks exercise clipping.
No runtime, decoder or instruction-semantics changes.

## Continuous callback, selection and source continuation

`E1M1AimRepeatProgram` merges the already decoded callback and parent program
with the authentic traversal setup and minimum-scan ranges. Its containment
lemmas check all overlapping supported offsets. Callback and repeated-selection
prefixes now compose in this single program without resetting memory, registers,
flags or the instruction pointer. The selection proofs reuse the established
minimum scan and callback-record facts, strengthening their combined result with
a frame for any word separated from the cursor store and pushed return word.

`E1M1AimRepeat.execution` executes an open two-sided line callback from
`0x2b760` through the actual parent decision. The clipped window determines
whether to stop; no continuation boolean is assumed. If open, the theorem derives
the consumed buffer encoding, runs the four-instruction counter head, full strict
minimum scan and range test, then reaches the next real indirect callback or an
exhaustion/rejection boundary. The total bound is `157 + 7 * hitCount` instructions.
Both clipped bounds survive selection and the CALL. The result uses the initial
callback slot and loop counter, with their preservation proved from memory frames.

`E1M1AimRepeatSource.correspondence` supplies the arithmetic premises from the
Lean heights and successful source divisions, and joins the machine result to
`E1M1AimIteration.next_line`. The live source continuation carries the same lower
and upper slopes plus the appended portal. Its selected path hit must align with
the source buffer record and the actual machine argument/saved pointer; the source
record replacement in the machine outcome is then identified exactly.

This does not establish that every source suffix index is the next minimum, nor
induct over every remaining hit. Next: relate the consumed buffer, visited prefix
and remaining iteration count, and carry all callback entry contracts through
successive iterations. Unified line exits, actor targeting and reachable-state
contract discharge remain open. Initial representation, separation/capacity and
successful division premises have not been silently replaced by test evidence.

Validation: `artifacts/e1m1-aim-repeat/validation.json`; strict transitive axiom
audit of the joined certificate, contract and byte mutation tests, and 384
independent original-x86 runs including actual height-dependent divisions,
changed bounds, full buffers, ties, wrapping stacks and all next-boundary cases.
No runtime, decoder or instruction-semantics changes.

## Consumed-hit preservation and next selection

`E1M1InterceptMark` connects the production ordered visitor's `set!` operation
to the actual 32-bit MAXINT fraction store. The theorem retains the complete
record encoding for arrays up to vanilla's 128-record capacity, including tags
and resolved pointers. Pointer resolution must be stable under changing the
selected fraction; a general resolver could otherwise encode that fraction.

`E1M1AimRecordFrame` derives record preservation through the complete open-line
callback, then combines it with the parent mark. It also carries protected words
through both parent branches and derives the reloaded cursor, restored stack,
loop counter and maximum from initial state. Separation is required against
all actual callback stack/global writes; no post-callback record image is assumed.

`E1M1AimNextSelection` proves the original four instructions at `0x2c83a`,
including testing the old counter after its wrapping decrement. Its `dispatch`
theorem composes that head with the previously proved full minimum scan, strict
tie rule, range gate and real indirect CALL. `after_callback` applies it to the
actual `E1M1AimResume.result` with the consumed buffer image and cursor derived
from callback entry. A zero iteration counter exits even when the collection
is nonempty. `carried_outcome` re-expresses the result using the initial counter
and preserved callback pointer, with explicit slot protection.

This is a next-selection bridge, not the whole ordered-hit induction. Its
callback continuation premise is supplied by the earlier window/line theorem
under successful-division and entry contracts. The callback prefix and the new
selection prefix currently use their respective authenticated programs, meeting
at exactly the same state. A common-program composition, source visited-prefix /
remaining-counter invariant, next callback map/global contracts, unified line
branches, actor hits and reachable-entry discharge remain to be joined.

Validation: `artifacts/e1m1-aim-next-selection/validation.json`; strict transitive
axiom audit, theorem-contract and original-byte mutation tests, and 384 independent
original-x86 callback/mark/repeat/scan/call checks. The new diagnostic isolates
the repeated-selection tail with equal-height sectors and compares every register,
every record word, cursor, bounds and callback slot. Prior diagnostics cover
clipping branches. No runtime, decoder or instruction-semantics changes.

## Open-line iteration and traversal resumption

`E1M1AimIteration` exposes the existing post-path loop as a single iteration
and a continuation with carried lower/upper slopes and portal history. Its
`live` theorem connects this extraction to `E1M1AimSource.afterPath`, already
connected to the production `Scene.aimLineAttack`. The `next_line` theorem
handles any selected open two-sided line, with divisions only when the relevant
sector heights differ. A closed or exactly equal clipped window stops at that
hit; an open window resumes with the updated state and remaining indices.

`E1M1AimResume.execution` composes the completed DOS callback with the actual
parent instructions at `0x2c86d`. Zero goes to `0x2c88c`; one marks the consumed
fraction `0x7fffffff` and returns to the selection loop at `0x2c83a`. The
clipped globals survive that mark under explicit entry-layout separation.

`E1M1AimLineJoin.correspondence` relates these paths using source heights and
source division results. The signed-word/Fixed conversion lemmas derive the
machine arithmetic premises; the callback's result is not assumed. The selected
record pointer must agree with the parent's saved EBX. The theorem proves
matching branch decisions, clipped globals and the selected-record mark, and
rewrites the live source continuation using the actual DOS return branch.

The next obligation is preserving the full hit-list/selection relation through
this resume and composing successive iterations. Actor hit processing and
reachable-entry contract discharge are still open. This does not prove an
entire aiming query or an arbitrary E1M1 input stream.

Validation: `artifacts/e1m1-aim-line-join/validation.json`; strict transitive axiom
audit and contract/byte mutation tests, plus 384 independent original-x86 runs
through the callback and parent branch. No runtime, instruction-semantics or
decoder changes.

## Aiming-window decision and callback return

`E1M1AimWindow.execution` joins the original two-sided open-portal callback from
entry (`0x2b760`) through its actual return to the caller, within 139 instructions.
The theorem derives the final lower and upper bounds and returns EAX=1 exactly
when `lowerAfter.toInt < upperAfter.toInt`. Equality returns zero. The comparison
uses the original CMP/JG signed-overflow semantics, not the sign of a wrapped
subtraction alone.

`OriginalAimWindow` pins the window test and both return tails. It proves the
3-instruction comparison followed by either 8-instruction return, including all
six POPs and RET. The routine decoder adds near signed JG (`0F 8F`) using the
existing `jumpSigned 2` semantics; a generic theorem checks arbitrary displacement
bytes and trailing code. No execution semantics or game runtime changes are made.

`E1M1AimReturnFrame` preserves the saved prologue words through the opening helper
and both clipping branches. Its additional separation premise concerns only
initial saved-frame addresses versus the opening/bound globals. Separation from
all helper stack writes follows from their distinct offsets, including wrapping
addresses. The composed theorem restores EBX/ECX/EDX/ESI/EDI/EBP, returns to the
original word at entry ESP, and advances ESP by four. Both aiming-bound outputs
survive the epilogue.

This completes the original machine path for an initially open two-sided line
under its explicit entry map/record, separation and successful-division contracts.
It is not yet the entire aim traversal: the complete live source iteration,
closed/open path unification, actor hits, parent ordered-selection continuation
and reachable-state discharge remain open. The earlier one-sided and closed
opening results remain separate theorems.

Validation uses `python3 scripts/verify_e1m1_aim_window.py` and the new window,
previous ceiling, and original floor-damage decoder regression suites. The full
proof build is rerun after extending the shared decoder. The certificate checks
42 pinned code ranges and audits the whole imported chain. Independent x86
execution adds 384 complete callback cases with both helper returns and both
callback return tails: 82 continue, 302 stop, 6 bound ties, 64 overflowing signed
comparison differences and 256 wrapping stack cases. It checks all eight
registers, actual return target, ordered writes, protected globals and the
modeled comparison/logical flags. These finite diagnostics support the model;
the universal claims are conditional Lean theorems.
Evidence: `artifacts/e1m1-aim-window/validation.json`.

Next compose the boolean/bound result with the live source line-hit iteration
and the enclosing ordered-hit selection loop, then handle actor hits.

## Both aiming bounds from callback entry

`E1M1AimCeilingEntry.execution` joins the complete floor/ceiling clipping portion
from `PTR_AimTraverse` entry (`0x2b760`) to the final window test (`0x2b800`), with
a bound of 128 instructions. It derives both final bound words:

- Lower: unchanged for equal floors, otherwise `max lower.raw floorSlope.raw`.
- Upper: unchanged for equal ceilings, otherwise `min upper.raw ceilingSlope.raw`.

`OriginalAimCeiling` pins the 47 original bytes for ceiling comparison, numerator
subtraction, distance reload, division CALL and signed upper-bound store.
`E1M1AimCeiling` executes the real existing `FixedDiv` helper and RET, derives
machine division safety from successful `checkedPathDiv`, and proves the update.
`E1M1AimClipFrame` establishes reusable floor-branch register and memory frames:
the line pointer, stack pointer and saved distance survive, as do words separated
from the actual stack/global stores. `E1M1AimCeilingEntry.inputs` uses those
frames to derive ceiling heights, computed opening top, eye height, old upper
bound and saved distance from callback-entry images. The final theorem also
proves that ceiling processing preserves the already updated lower bound.

The entry representations, static separation and conditional source division
success remain explicit. This is not yet a theorem about the entire live source
hitscan iteration or reachable E1M1 queries. The final signed window decision,
callback return, actor branches and ordered-loop composition remain open. The
next original branch at `0x2b80b` uses near `JG` (`0F 8F`); the shared routine
decoder currently lacks that encoding. Add and validate that decoding before
joining the final window decision and its two return paths. No decoder or
instruction semantics were changed in this batch.

Validation: `python3 scripts/verify_e1m1_aim_ceiling.py`,
`PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_aim_ceiling test_e1m1_aim_floor`.
The certificate authenticates 40 code ranges, rechecks the division bytes, and
audits all imported and new declarations. Six new tests reject altered branch,
distance and helper bytes, missing separation/entry images/division success,
wrong max/min updates and wrong endpoints. Independent x86 diagnostics add 384
continuous callback cases, checking both real helpers, all eight registers,
ordered writes and protected globals. Coverage includes 64 equal ceilings,
269 normal and 51 saturated ceiling divisions, 158 negative ceiling quotients,
128 tightened upper bounds, 256 unchanged upper bounds, 45 exact upper-bound
ties, 256 cases with both divisions, 192 negative distances and 256 wrapping
stacks. These diagnostics support the model; universal claims are the conditional
Lean theorems. Evidence: `artifacts/e1m1-aim-ceiling/validation.json`.

## Floor aiming bound from callback entry

`E1M1AimFloorEntry.execution` extends the continuous open-passage callback proof
from `0x2b760` through `0x2b7d1`, with a bound of 90 instructions. It joins three
pieces:

- `OriginalAimFloor` authenticates and executes the 43-byte floor comparison,
  numerator subtraction, division CALL, signed slope comparison and optional
  lower-bound store. Equal floors jump directly to the ceiling stage.
- `E1M1AimFloor` includes the existing original `FixedDiv` implementation, proving
  the real helper saves, arithmetic, RET and caller continuation. Successful
  `checkedPathDiv` supplies the quotient and discharges IDIV safety. The old lower
  bound survives all four CALL/helper stack writes under explicit separation.
- `E1M1AimFloorEntry` derives map floors and opening bottom from the original entry
  image, preserves eye height and lower bound, reuses the proved distance product,
  and joins the exact `max lower.raw slope.raw` update to the original callback.
  Equal floors need no successful-division premise.

This is the operation in `Doom/Hitscan.lean`'s lower-window update, but it does not
yet compose the entire source hitscan iteration. Initial map/record images and
static memory separation remain assumptions. The successful source division
premise is conditional on unequal floors and has not been proved for all
reachable query states. The ceiling branch, final empty-window test, callback
return and actor branches remain open.

Validation: `python3 scripts/verify_e1m1_aim_floor.py`,
`PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_aim_floor test_e1m1_aim_distance`.
The certificate checks 39 authentic ranges, rechecks the reused division bytes,
and audits the full imported theorem chain. Six new tests reject altered bytes,
missing images/separation/source arithmetic, wrong max/min and wrong PC claims.
Independent x86 execution adds 384 full callback-to-floor cases (77 equal-floor,
231 normal division, 76 saturated division, 147 negative quotients, 140 raised
bounds, 244 unchanged bounds, 44 exact slope/bound ties, 256 wrapping stacks,
57 wrapped subtractions). It checks actual helper RETs, all eight registers,
ordered writes and protected operands, with no callbacks or helper stubs.
These tests diagnose the model; the conditional universal claim is the Lean proof.
Evidence: `artifacts/e1m1-aim-floor/validation.json`.

Next connect the ceiling slope and upper-bound update, then the final window
comparison and return, and compose these updates with the actual source hit loop.

## Callback-entry map transport and aim distance

`E1M1AimOpeningFrame` closes the interior map-image assumption introduced by the
opening-height proof. Its `Image` contains the back-side sentinel check, front/
back sector pointers and four heights. `transport` carries that image from
callback-entry memory through the six register pushes and actual CALL push.
`helper_safe` derives read separation for the helper's four additional saves
and global stores from an entry-level contract. `decision` therefore obtains
the actual opening branch from the original callback-entry image, not from
assumed helper outputs. `E1M1AimMapped.execution` joins this with the continuous
48-instruction-bound prefix; `closed_correspondence` starts the DOS side at
`PTR_AimTraverse` entry and gives the same first-closed-line live Lean result.

`output_frame` preserves any protected word through both prologues, the CALL,
helper globals and the opening gate. `output_regs` recovers the selected record
pointer in EDX and callback stack position. `E1M1AimDistance.operands` uses these
facts to derive the attack range at `0x2b9b8` and the selected intercept fraction
from callback-entry memory. Neither input is assumed at the multiply boundary.

`OriginalAimDistance` authenticates 15 bytes at `0x2b797..0x2b7a6`: load range,
load fraction, signed IMUL, SHRD by 16, and move the result to EDX. Its arithmetic
proof reuses `BlockSummary.multiply_correct` and the original universal Fixed.mul
proof. `E1M1AimDistance.execution` joins the real open-passage path through those
five instructions. Within 53 instructions from callback entry, EAX and EDX both
equal `(distance * hit.frac).raw.toBitVec`; memory is unchanged by the product.
Negative inputs and wrapping result bits are covered without magnitude bounds.

Initial record/map encoding and static separation remain input contracts. This
batch derives the later helper image and operands, but does not yet discharge
those initial contracts from query-entry/reachable state. The closed source
correspondence still needs the ordered first-hit relation. Next connect the
front/back floor comparison, original slope division and lower-slope update,
then the ceiling path and final window test. Closed callback epilogues, query
return, actor targeting and repeated selection remain separate obligations.

Run `python3 scripts/verify_e1m1_aim_distance.py`. The certificate contains 38
authenticated ranges and 828 map cells, auditing 902 declarations against only
`propext`, `Quot.sound` and `Classical.choice`. Tests reject changed range-load,
multiply and shift bytes, missing map images/read protection, lost entry operand
contracts, an unjustified open branch, wrong product claims and wrong PCs.
Independent x86 diagnostics pass 768 cases without stubs: the preceding 384
opening cases plus 384 open-passage distance cases. The latter include 152
negative products, 192 overflowing results, 78 zero-operand cases and 256 wrapping
stacks; exact registers, instruction path, writes, record/range and return word
are checked. Evidence: `artifacts/e1m1-aim-distance/validation.json`. All 116 Doom
sources tracked by the preceding validation remain unchanged. Runtime, decoder
and instruction semantics are unchanged.


## Aiming sector-opening call

`OriginalAimOpening` authenticates the next 24 aim bytes, `0x2b77f..0x2b797`:
move the line pointer into EAX, CALL `P_LineOpening`, load `openbottom`, compare it
with `opentop`, and branch on the signed comparison. The closed exit is `0x2b8d2`;
the open exit is `0x2b797`, before distance multiplication and slope clipping.
The branch compares the bounds directly, not the wrapping `openrange` subtraction.

`E1M1AimOpening.execution` reuses the complete `E1M1NoiseOpening.opening_execution`
proof of the same original helper, including its RET. Static global/stack
separation derives the real return destination `0x2b786` and preserved ECX, EDX
and ESP. Its bound is 36 instructions. `from_callback` joins the preceding 12
instructions from `PTR_AimTraverse` entry: real register saves, record tag, line
pointer and two-sided flag. The combined bound is 48; neither helper output nor
post-return state is a premise. Static record/flag/prologue separation remains.

`E1M1OpeningHeights.heights` derives the helper's signed minimum ceiling and
maximum floor from its entry-side index, sector pointers and heights. Its read
separation includes the helper's saves and global writes; the side index must
not be the missing-back-sector sentinel. `height_decision` feeds those derived
bounds into the actual aim branch. `E1M1AimPortalSource.signed_bounds` connects
that word-level comparison to the production Fixed/Int32 predicate for all
32-bit heights. `first_closed` and `blocked_query` prove that the live aim loop
stops on a first closed two-sided opening, before division or slope clipping.
`closed_correspondence` combines that live result with the real call/helper/gate
execution, under explicit helper-entry map encoding and ordered-first-hit inputs.

The next batch, described above, now transports this map image through the
callback prologue/CALL and connects the open-passage distance product. Joining
the closed gate through the callback epilogue and parent traversal stop, and
proving open-portal slope clipping, remain open. The earlier one-sided complete callback
proof remains unchanged. Next connect the opening/record frame to the clipping
arithmetic and close the remaining line callback branches, then actor handling,
repeated ordered-hit processing and the query/caller returns.

Run `python3 scripts/verify_e1m1_aim_opening.py`. The certificate includes the
reused 106 helper bytes and the 24 new caller bytes: 37 authenticated ranges,
828 map cells, and 880 audited declarations. Tests reject modified CALL/branch/
helper bytes, lost stack/read separation, missing input images, reversed signed
min/max choices, incorrect source stop counts and missing ordered-path agreement.
Independent x86 execution passes 384 cases without call stubs, checking exact
registers, modeled flags, memory writes, records and return words. Coverage
includes 340 closed and 44 open cases, 65 equal-bound cases, and 90 cases where
testing the wrapping height difference would disagree with the actual branch.
Evidence: `artifacts/e1m1-aim-opening/validation.json`. All 107 Doom sources tracked
by the preceding validation remain unchanged; runtime, decoder and instruction
semantics are unchanged.


## One-sided aim wall stop

`OriginalAimGuard` authenticates two new DOS ranges: the callback prologue and
line/thing/one-sided guards (`0x2b760..0x2b77f`), and its false-return epilogue
(`0x2b8d2..0x2b8db`). It proves the nine-instruction type split, three-instruction
line flag test, and eight-instruction false return, using the actual bytes.
The type split sends a zero tag to the thing branch; a line with flag bit 4 set
reaches the opening-helper call boundary. Neither remaining body is executed yet.

`E1M1AimWall` carries the selected record through six register pushes, derives the
wall pointer and flag from entry memory, and proves stack restoration and the
actual RET destination. Modular separation lemmas include wrapping stack
addresses. `E1M1AimStop.execution` joins this 20-instruction callback to the four
instructions taking the parent traversal's false branch. The result is EAX zero,
ESP advanced past the return word, exactly the six prologue memory writes, and
PC `0x2c88c`. No callback result or post-return state is an input premise.
`from_ready` obtains the selected record, callback PC and return word from the
previous `E1M1CallbackEntry.Ready` result. The new static prologue separation and
one-sided flag premises still need discharge from the surrounding state relation.

`E1M1AimSource.live` exposes the actual production `Scene.aimLineAttack` by
kernel-checked definitional equality, including its path query and aim loop.
`first_wall` proves that a first one-sided wall stops immediately without a target;
`blocked_query` lifts this to the live function. `E1M1AimStop.correspondence`
combines that result with the real DOS stop path. Its successful path query,
shared ordered first hit, and map-flag encoding are explicit interface premises,
not consequences yet of `E1M1QueryCallback.execution`. This closes one conditional
callback case, not the full query or all aiming.

Run `python3 scripts/verify_e1m1_aim_stop.py`. The certificate authenticates 35
byte ranges and 828 map cells and audits 857 declarations transitively against
`propext`, `Quot.sound` and `Classical.choice` only. Tests reject changed guard/return
bytes, missing record/flag/stack contracts, wrong return addresses and instruction
counts, missing first-hit agreement, and drift from the live source guard/count.
Independent original-x86 diagnostics cover 384 cases: 128 thing splits, 128 open
line boundaries, and 128 full one-sided wall returns with the parent stop branch.
They check registers, modeled flags, stack writes, return words and records without call stubs.
Evidence: `artifacts/e1m1-aim-stop/validation.json`. All 103 Doom sources tracked
by the preceding validation remain unchanged; runtime, decoder and instruction semantics are unchanged.

The opening helper and signed closed-opening gate are now connected as described
above. Next connect portal aim clipping, then the actor branch
and repeated ordered-hit processing. Discharge the new interface premises from
the query/map relation and join the existing query epilogue and enclosing callers.


## Query-to-callback readiness

`E1M1QueryCallback.execution` strengthens the continuous first-dispatch result.
The callback destination is the argument read from query-entry memory at
`q.sp - 44`; the reached stack is `q.sp - 140`, with return word `0x2c86d`.
The source-selected record pointer is in EAX, and the entire collected array
still encodes its original fractions, line/thing tags and resolved pointers.
`E1M1CallbackEntry.selected_record` exposes the selected record at that actual
EAX address in the callback's current memory.

Three connections supply this result. `E1M1SelectionFrame` carries ESP through
every original minimum-scan iteration alongside the existing register/memory
facts. `E1M1CallbackEntry` proves that the cursor store and CALL push preserve
all record words, derives the indirect destination from the saved slot, and
establishes the real return word. `E1M1QueryCallback.collection` retains the
existing collection frame, allowing the query argument to be transported from
entry memory rather than supplied at a future state. The total instruction
bound remains `207 + bound q cells + 7 * after.collected.size`.

`aim_argument` reuses `OriginalAimSetup.stored_callback` to prove the aim caller
places `0x2b760` in the query argument slot. `specialize_aim` connects that initial
argument to the continuous result; `aim_destination` yields either the no-hit
exit `0x2c887` or `PTR_AimTraverse` entry `0x2b760`. This does not execute the
callback's body or close the enclosing aim/firing caller.

The added `CallbackSafe` premises are static separation for the argument through
initialization/collection and for records against the final return push. The
cursor/record separation is proved for all 128 buffer slots; separation of the
saved target from the cursor follows from the existing selector-stack contract.
No dynamic callback result or intermediate record image is assumed. Reachable
layouts must still discharge these static contracts.

The strict certificate keeps the same 33 byte ranges and 828 map cells. Tests
reject changed CALL bytes, missing memory/stack contracts, wrong argument slots
and return addresses, and unjustified fixed callback identities. Concrete
aliasing examples demonstrate corruption when the required separation is
removed. The original-x86 diagnostic is rerun for 516 collection-exit-to-dispatch
cases, retaining its explicit scope; query collection is proved in Lean rather
than rerun by that diagnostic. Evidence:
`artifacts/e1m1-query-callback/validation.json`. Runtime, decoder and instruction
semantics are unchanged; all previously tracked Doom sources remain unchanged.

The one-sided wall case is now executed by `E1M1AimStop`, described above. Next
establish portal and target clipping from this reached state. Then connect sentinel
replacement, subsequent selection passes and query return. Existing budget,
entry, map-image and reachable-state obligations remain.


## Continuous first-intercept dispatch

`E1M1QueryDispatch.execution` joins query entry `0x2c8a0`, initialization,
collection, selector setup, the exact minimum scan, the range gate and the
original indirect CALL into one machine prefix. Its bound is
`207 + bound q cells + 7 * after.collected.size`. The source collection and
production visitor tail remain in the conclusion. All intermediate states come
from executed instructions; the composition adds no new input premises to
`E1M1TraversalEntry.execution`.

`E1M1FirstIntercept.Boundary` distinguishes an empty collection, a minimum beyond
65536, and an admitted minimum. The first two reach `0x2c887`. The admitted case
carries the exact live-source minimum, its in-bounds index, EAX equal to that
record's address, and the exact state after the real indirect CALL. It does not
claim that the callback target has been identified or that its body has run.
`empty_tail` and `rejected_tail` prove the corresponding source no-hit results
unchanged for any visitor, including the existing visited list and completion
flag. Equality at the range endpoint is admitted, and tied hits retain the
original strict-minimum ordering.

The new certificate reuses all 33 authenticated ranges and 828 map cells; it
adds no decoder or instruction-semantic changes. The independent x86 diagnostic
runs the collection-exit caller, setup, scan, gate and CALL continuously for 516
cases across all counts zero through 128. It checks exact registers, writes,
instruction counts, unchanged record memory and exit PCs without callback
stubs. This diagnostic starts at collection exit; collection itself is covered
by the Lean theorem. Contract and byte-mutation tests check the joins, bounds,
cutoff, and empty/rejected source tails. Evidence is in
`artifacts/e1m1-query-dispatch/validation.json`.

The subsequent `E1M1QueryCallback.execution` now derives callback readiness,
including the initial argument, full record image and return word. The callback's
clipping/target behavior, encoded sentinel replacement, repeated selection and
return remain. Existing capacity, entry, map-image and stack-separation contracts
still need reachable-state justification; this is not complete aiming or
whole-game equivalence.


## Collection to selector entry

`E1M1TraversalEntry.execution` extends the continuous query theorem from
`P_PathTraverse` entry `0x2c8a0` through the collection exit and original
`P_TraverseIntercepts` call/prologue/count calculation. It retains the actual
production collection, its ordered-hit tail and the collection invariant. The
instruction bound is `198 + bound q cells`, adding exactly 23 instructions to
the prior initialization-and-collection theorem.

The new original ranges are `0x2cafd–0x2cb0b` (load callback/maxfrac and CALL)
and `0x2c810–0x2c841` (prologue, count calculation and first outer-loop guard).
`OriginalInterceptSetup.byte_distance` proves pointer subtraction gives
`12 * count` without signed wrap for count at most 128. `count_execution` proves
the real sign extension and signed divide recover the exact count with zero
remainder. The original post-decrement is retained: an empty list leaves ESI
at `0xffffffff` but exits before scanning, whereas nonempty lists reach
`0x2c841` with ESI equal to count minus one.

`E1M1InterceptSetup.frame` protects a word from all six stack writes;
`records` lifts this to fraction, kind and pointer fields of every collected
intercept. `E1M1TraversalEntry.from_collection` derives count, cursor and encoding
from the existing final collection invariant, rather than assuming a prepared
selector state. Its additional `Protected q` contract is static separation from
the deeper selector stack frame; this remains a reachable-layout obligation.
The callback value is loaded from the actual stack argument and saved in the
selector's local slot. Its identity and behavior are not assumed proved.

The shared instruction decoder gains only the previously unsupported `0x4e`
(`DEC ESI`) form. It reuses the existing wrapping add-immediate register semantics,
invalidating flags; the following original `TEST EAX,EAX` supplies the flags
used by the branch. Game runtime code and prior proof sources are unchanged;
the dependent proofs are rebuilt for this decoder extension.

`scripts/verify_e1m1_traversal_entry.py` authenticates both ranges, file offsets
and relocations and extends the strict transitive axiom audit. Its optional x86
diagnostic checks every count from zero through 128, arbitrary incoming register
values, all six writes, unchanged records/cursor, exact exit PCs and the
23-instruction bound, without callback stubs. Tests reject changed bytes,
missing count/cursor/stack contracts and altered entries or empty-list behavior.
Evidence: `artifacts/e1m1-traversal-entry/validation.json`.

The subsequent `E1M1QueryDispatch.execution` now composes this result with the
minimum scan, distance gate and first callback entry. Aim callback readiness and
clipping/target behavior, encoded sentinel replacement and the repeated ordered-hit
loop remain. Return/retry, caller integration and reachable-state contracts also
remain.

## Original intercept distance and callback boundary

`E1M1InterceptGate.execution` extends the exact minimum scan continuously through
`0x2c85e–0x2c868` or the out-of-range exit `0x2c887`, with bound
`7 + 7 * array.size`. It preserves the caller's EDI maximum through the scan,
then relates the actual signed comparison against 65536 to the live tail's
cutoff. Equality is admitted. `no_choice` proves the maximum-distance sentinel
exits before DOS can use the stale EBX pointer.

`admitted` derives a real in-bounds index from the live minimum result and the
cutoff. `callback` joins the gate to the actual `CALL [ESP]`: EAX is the selected
record address, the target comes from the current stack slot, and the original
return address is pushed. This is a callee-entry theorem, not a contract that
assumes the aim callback is correct. It does not yet establish which callback
was installed by the enclosing query caller.

`OriginalInterceptGate.resume_execution` proves both paths beginning at the
actual callback return site `0x2c86d`. Zero reloads ECX and exits at `0x2c88c`
without a sentinel write; any nonzero return reloads ECX, writes `0x7fffffff`
at EBX and reaches the outer-loop gate `0x2c83a`. The cursor reload uses the
post-callback memory, not a pre-call cached value. These are exact machine-state
results. They do not yet prove source-array encoding after the write, the
callback entry-to-return execution, or repeated ordered processing.

The new byte range retains original file mapping and all three relocations.
`scripts/verify_e1m1_intercept_gate.py` extends the strict transitive axiom audit
to 31 ranges. Its optional independent x86 diagnostic executes the combined
scan/gate/call up to real callee entry, and separately both post-callback paths
from arbitrary returned states, without callback stubs. It checks registers,
write addresses/values and exit PCs; the relocated return address is checked
using the emulator's code origin. Contract mutations reject missing bounds,
encoding, maximum, selection and cutoff premises, as well as altered bytes,
endpoint behavior, callback argument and entry/exit PCs.

Evidence: `artifacts/e1m1-intercept-gate/validation.json`. Prior proof sources,
runtime code and instruction semantics were unchanged in that milestone. The
subsequent query-to-selector theorem above now covers the collection-exit call
and selector prologue/count setup. Composition with the scan, the aim callback
and the source effect of sentinel replacement still precede repeated passes.

## Original nearest-intercept selection

`E1M1MinimumScan.execution` connects the original signed strict-minimum scan at
`0x2c841–0x2c85e` to the selector inside the live `visitHits` tail. It covers every
encoded array with at most 128 records. The theorem starts with ECX at the actual
array end and encoded fraction words; it executes the original distance reset,
unsigned pointer guard, record comparisons and backward branch. The output
includes the exact source minimum result, selected pointer when a choice exists,
array-end position, original exit PC and equality of the entire byte memory.
Its bound is `4 + 7 * array.size` modeled
instructions. The scan itself writes no memory.

`E1M1InterceptMinimum.live` exposes the exact production selector without a
runtime change. `minimum_replay` joins its actual range-based loop to a structural
recursion, and `E1M1MinimumScan.next` connects each real DOS iteration to one
source update. Strict signed comparison retains the first equal-distance hit.
Empty and sentinel-only arrays are included. In the latter case DOS retains its
old best-pointer register; the representation constrains that register only when
the source selects an index. `minimum_none` proves that no selection leaves the
maximum signed-distance sentinel. The subsequent distance/callback-boundary proof above now verifies the DOS cutoff gate.

The collection result supplies record encoding through the reusable `fractions`
lemma. The subsequent query-to-selector theorem above now proves the continuous
handoff through the actual `P_TraverseIntercepts` call, saves, count division and
initial outer-loop guard. Its result must still be composed with this scan and
the cutoff/callback boundary. Callback effects, encoded sentinel replacement,
the outer repeated-selection loop, aim clipping and query return/retry remain.
Do not describe this as full ordered-hit or full aiming correspondence.

The new range is extracted from the pinned executable with its original file
mapping and data relocation checked. `scripts/verify_e1m1_minimum_scan.py` extends
the strict transitive axiom audit to 30 code ranges. Its `--cross-check` option
runs the extracted scan in Unicorn without callbacks/stubs, checking every
register, unchanged memory and instruction counts across signed, tie, empty,
sentinel and full-capacity cases. This is diagnostic evidence, not the proof.
Contract/mutation tests also reject changed bytes, ties, sentinel, encoded
memory, limits, bounds and exit state. Evidence is recorded in
`artifacts/e1m1-minimum-scan/validation.json`. Runtime and instruction semantics
are unchanged; reachable-state contracts remain open.

## Continuous query initialization and collection

`E1M1QueryCollection.execution` joins actual DOS initialization and the full
collection loop into one authenticated execution from `P_PathTraverse` entry
`0x2c8a0` to collection exit `0x2cafd`. The numeric route is generated from the
source initialization, and its collection is the loop inside `Scene.pathTraverse`.
The result retains the complete source collection, visit history, numeric state,
map and callback images. The bound is at most 175 setup instructions plus the
existing per-cell instruction bound; no emulator timing claim is made.

The new pieces are:

- `E1M1QueryImages`: entry payloads describe only existing line geometry, object
  geometry, links and selected table heads. They do not assume the future trace
  or active-global values. Those come from the actual initialization writes and
  survive axis setup. Map data and the caller's option word also reach the gate.
  Outside cells require no payload.
- `E1M1QueryPrefix`: original initialization, both axis calculations, both
  intercept setups and their helper calls compose into the same authenticated
  program as the loop. Division safety comes from successful production axis
  calculations. It adds no original byte range or machine semantics.
- `E1M1QueryCollection.state`: derive the full gate invariant from entry memory,
  including map/options, stack, empty collection and next-epoch visit history.
  `execution` combines this with all derived cell images and the existing loop
  theorem. No gate-state or gate-image premise is supplied.

For any source visitor, the complete live query is now exactly its ordered-hit
tail applied to the resulting collection. `query_tail` makes that boundary
explicit and preserves source errors/early visitor termination. It does **not**
prove original DOS ordered visitation. That selection loop and aim clipping are
the next correspondence target, followed by query return/retry.

Entry geometry, successful axis calculations, actual map/object encodings,
next-epoch freshness, separation, static callback arithmetic, scene relations and
aggregate capacity remain explicit contracts. Reachability must still establish
them; this theorem is not universal E1M1 parity. It starts at `P_PathTraverse`,
not the enclosing aim-ray prologue or firing callback; those earlier callers
still need joining to this complete collection result.

Validation: `scripts/verify_e1m1_query_collection.py` extends the strict transitive
axiom audit over the same 29 pinned original code ranges and 828 map cells.
Tests reject weakened payload/protection/option contracts, changed entry/exit,
wrong visit history/final coordinates and enlarged capacity; kernel fixtures
check strict-min ties, the range cutoff and source visitor termination. Runtime
and instruction semantics are unchanged; no additional emulator cross-check is
claimed. Evidence is in `artifacts/e1m1-query-collection/validation.json`.

## Query-entry preparation

`E1M1QuerySource.live` now decomposes the actual aiming query into `prepare`,
`runPrepared` and `visitHits`, without changing production code. This equality
covers invalid profiles, X-before-Y axis setup, all errors, collection's early
return channel and the exact strict-min ordered visitor tail. The prepared
numeric state is the same `E1M1FiringGridState.initial` already used by the
original setup proofs; the loop is `E1M1LiveWalk.source`, not a new traversal.

`E1M1QueryInit` reuses those setup proofs to establish, from query-entry memory:

- All eleven numeric fields, the collection entry PC and the stack position.
- An empty intercept-buffer representation: initialization really resets the
  cursor, and axis setup preserves it. Old cursor/record contents are arbitrary.
- The all-false source visit array represented by original line stamps at the
  incremented epoch, given protected stamps and freshness at that next epoch.
  Old-epoch freshness alone is insufficient, especially on counter wrap.

`E1M1QuerySource.initialized` assembles these facts with successful production
preparation. It does not introduce reached-gate image or visit assumptions. The
remaining entry contracts are explicit geometry, successful divisions, memory
separation and next-epoch freshness. They still require reachable-state proofs.

This is an initialization-state join, **not yet a continuous execution theorem
from query entry through collection exit**. Next assemble the map/options and
per-cell payload images from entry memory, use the initialized facts to build
`E1M1CellWalkInvariant.State`, and compose the existing setup prefix with
`E1M1LiveWalk.execution`. Then connect DOS ordered hit selection and aim clipping.
Aggregate capacity and the other reachable-state contracts remain open.

Validation: `scripts/verify_e1m1_query_init.py` extends the strict transitive axiom
audit over the same 29 pinned code ranges and 828 map cells. The query tests
reject changes to initialized history, axis assignment, iteration budget,
errors, strict-min tie handling, division success and memory/freshness contracts.
They also kernel-check empty preparation, boundary nudges and invalid profiles.
Runtime and instruction semantics are unchanged; no new emulator run is claimed.

## Collection correspondence with the live grid loop

This batch closes the source-fragment gap for aiming's grid collection.

- `E1M1TraversalLoop.live` exposes the grid loop by definition-level equality
  with the complete production `Scene.pathTraverse`, for all flags. The loop
  retains the actual early-return channel and line/object error paths. The
  surrounding initialization, profile checks and strict-min visitation are
  retained exactly. `live_aiming` uses the previously checked aiming scan.
- `E1M1LoopReplay.aiming_body` identifies each actual aiming iteration with
  logged cell collection followed by endpoint/axis control, including errors.
  `finish_pack` relates the signed Int32 operations to the checked word step,
  preserving wrapping arithmetic and first-axis priority. `callback_step`
  establishes preservation of immutable loop parameters.
- `replay` and `walk_replay` induct over the real finite iteration sequence.
  They prove equality to generated-route collection for arbitrary budgets,
  numeric states, visited histories and initial results. They retain both the
  source error result and, on success, the complete mutable loop state. No
  map-validity or capacity assumption is needed for this source equality.
- `E1M1LiveWalk.execution` composes that equality with authenticated DOS
  execution. It reaches the original collection-loop exit and returns the
  actual source loop's result, including final coordinates/intercepts, hits,
  logs and history, with no early return. Existing scene/memory contracts and
  the shared aggregate budget remain prerequisites of DOS correspondence.

**Remaining boundary:** query-entry initialization still needs joining to the
collection gate. Reachable scene/machine encodings, geometry, arithmetic,
separation and sufficient capacity remain to be discharged. The source loop
is now connected; the following DOS ordered intercept processing, aim clipping,
query return/retry and complete tic are not proved by this join. Retaining
source hit visitation in `live` is not a DOS correspondence theorem for it.

Validation is recorded in `artifacts/e1m1-live-walk/validation.json`. The
certificate extends the same 29 byte ranges with a strict transitive axiom
audit. Mutation tests reject drift in the real loop's budget, leading-zero
line ID, logs, endpoint condition, axis choice, errors and later hit visitation.
Kernel fixtures check stalls, endpoint collection, deduplication, signed wrap
and error propagation. DOS contracts, final numeric state and history remain
explicitly tested. Runtime and instruction semantics are unchanged; no new
emulator run is claimed.

## Generated traversal route and loop exit

`E1M1GridRoute.route` now constructs the itinerary from the numeric gate state.
The selector only supplies cell metadata: its coordinates are overwritten by
the numeric state, so it cannot steer the walk. `follows` derives every
coordinate and intermediate continuation; `length_bound` bounds all generated
routes, including repeated cells and stalls.

`source_eq` proves that, for any legal counter 0..63 and exactly its remaining
budget, the DOS continuation-PC rule chooses the same route as an
endpoint/budget controller. `exits` proves that the generated route reaches
0x2cafd, whether the endpoint is reached early or the counter is exhausted.
The endpoint cell is processed before exit. The legal counter and matching
budget are necessary: stopping after an arbitrary prefix does not imply exit.

`E1M1GeneratedWalk.execution` joins this route to the logged collection theorem.
Its premises no longer include an arbitrary itinerary or `Follows`. It produces
one continuous authenticated DOS execution through the original loop exit,
exact source collection over the generated route, full result/history, numeric
state, preserved reads and persistent images. The source scene relations,
per-cell metadata contracts and one aggregate capacity bound remain explicit
premises over the generated route.

**Remaining boundary:** this begins at the collection gate, not the query entry.
The endpoint/budget route still uses the checked bitvector step. Identifying its
finite collection replay with the actual Int32 production loop, and connecting
query initialization to the starting gate, remain open. Existing numeric-axis
and actual-function equalities should be reused for that join. No full aiming,
reachable-budget sufficiency or whole-tic claim is made.

Validation is recorded in `artifacts/e1m1-generated-walk/validation.json`.
The strict certificate extends the same 29 DOS ranges. Tests cover early
endpoints, full-budget stalls, axis priority, signed-coordinate wrap, metadata
independence, counter/budget mismatch and retained machine/scene/history
contracts. The preceding logged-walk suite and broader proof build are rechecked.
Runtime and instruction semantics are unchanged; no new emulator run is claimed.

## Logged source collection across the admitted walk

This batch replaces the machine walk's abstract per-cell collection relation
with executable source collection, while preserving the original numeric and
memory conclusions. The one-tic obligation remains autoaim during firing.

- `E1M1CellLineSource.lines` derives the line-scan entry, payload readiness,
  mixed-record reserve and visited representation from the actual cell gate.
  Its source scene relation ties raw line IDs and geometry to the Lean arrays.
  The line result is the same collector already connected to the live traversal.
- `E1M1CollectionLog` proves that block logging commutes with bounded append
  and the source line loop, including error behavior. Logging also preserves
  the machine record/stamp relation. No gameplay state is changed by this
  proof-level bookkeeping.
- `E1M1LoggedCell.one` joins the line result with the checked object scan and
  the actual grid step. The executable cell operation logs lines, scans lines,
  logs objects, then scans objects. Outside cells log both visits without
  consulting cell arrays, leave hits/history unchanged and spend no capacity.
- `E1M1LoggedWalk.execution` composes these results across a finite mixed
  inside/outside itinerary. Its output includes one continuous authenticated
  DOS prefix, exact source collection result, complete `PathResult`, updated
  history, hit-count bound, original numeric state and PC, preserved reads and
  all initially supplied images. A shared initial budget is consumed across
  cells; duplicates keep their existing seen state even when a cell repeats.

**Remaining boundary:** the source replay consumes an admitted itinerary.
`Follows` still supplies the coordinates and intermediate continuation facts.
No new theorem constructs the full route for every reachable query or proves
that `E1M1LoggedWalk.collect` is the complete live grid loop. The next join must
construct the itinerary from initialized numeric state and identify the source
replay with the live controller, including endpoint and 64-iteration exits.
The previous actual-function equality remains available for that join. Geometry,
scene/machine lookup relations, memory separation and aggregate capacity remain
explicit initial conditions. There is no full DOS traversal or aiming claim.

Validation is recorded in `artifacts/e1m1-logged-walk/validation.json`. The same
29 authenticated byte ranges and strict axiom audit are extended. New tests
check gate/scene prerequisites, dimensions, initial images, route, shared budget
and persistent history; kernel fixtures cover outside logging, repeated-cell
logging with line deduplication, and full-buffer error/preservation. The previous
live-traversal suite and broader proof build are rechecked. Runtime and machine
instruction semantics remain unchanged; no emulator comparison is added here.

## Checked collector inside the live traversal

This closes the source-fragment gap identified in the preceding line-scan join.
The one-tic obligation remains the autoaim query during pistol/shotgun firing.

`E1M1TraversalSource.withLines` exposes the line-cell scan within the complete
production traversal. `live` proves exact equality with `Scene.pathTraverse`
for all flag settings, scenes, endpoints and visitors. The proof normalizes
Lean's generated match expressions; it does not alter the runtime function or
introduce a new axiom. The exposed scan's result retains the early-return value,
current `PathResult` and visited array, matching the nested loop's actual control
flow. Invalid IDs, lookup failures, arithmetic errors and overflow remain errors.

`aiming_flow_list` / `aiming_flow` prove that at flags 3 this interface equals
the existing `E1M1LineSourceLoop.lineCell` result with no early-return value.
`live_aiming` substitutes that proved collector into the entire traversal. The
source equality needs no successful lookup, sufficient capacity or valid-map
hypothesis: it also agrees on failures. The surrounding profile checks, raw
leading-zero ID, block logs, object loop, 64 iterations, endpoint/axis priority,
strict-min selection and visitor stopping behavior remain exactly those in the
live definition. The theorem must be rechecked against actual runtime changes.

`E1M1TraversalLineJoin.execution` joins the authenticated DOS per-cell line scan
to this precise callback interface. It reuses the previous record/stamp and
source-lookup contracts, with no new reached-callback or desired-output premise.
The machine result remains conditional on the existing initial encodings,
geometry/fractions, layout, history and capacity reserve.

**Remaining boundary:** the source-level enclosing traversal equality is now
proved, but full DOS-to-Lean traversal is not. The admitted machine itinerary
must still be constructed from initialization and connected to source grid state,
block logging and object iteration. The line phase's callback contract is ready
for that composition. General candidate-budget sufficiency and reachable-state
contracts remain open. Then connect DOS ordered intercept processing, portal and
target clipping, and the final aim result/retries. Retaining the existing source
hit-order loop in an equality is not a proof that DOS hit ordering matches it.

Validation is recorded in `artifacts/e1m1-traversal-source/validation.json`.
The strict certificate extends the same 29 DOS byte ranges and axiom audit.
Tests reject changes to the iteration bound, raw leading zero, block logs,
strict tie comparison, visitor stopping polarity, aiming flags and machine
contracts. Concrete kernel-checked fixtures distinguish early-out flags from
aiming flags and retain errors/duplicate validation. The preceding line-source
suite and broader proof build are rechecked. Runtime and instruction semantics
are unchanged; this batch adds no independent emulator comparison.

## Line scan to aiming source loop

The one-tic obligation is still the autoaim query inside pistol/shotgun firing.
This connection identifies the checked DOS line scan's output with the aiming
line-cell source fragment used by `Scene.pathTraverse`, under its existing
initial contracts. It does not close the entire query or introduce runtime
behavior changes.

- `E1M1LineCollect.visit_step` joins stamp-based duplicate detection and the
  machine's crossing/rejection branches to a Boolean seen array, production
  `Collision.lineIntercept`, and production `Collision.appendIntercept`.
  `collect_run` composes that result across the entire candidate list using the
  existing invariant and capacity reserve.
- `E1M1LineSourceLoop.source_collect` proves the mutable `for` loop agrees with
  that collector. It retains the signed-ID guard and scene lookup before the
  duplicate test. The theorem holds for successful and error results, provided
  IDs and scene lookups are valid. It preserves the input order and repetitions.
- `E1M1LineSourceScan.execution` joins the source result to the authenticated DOS
  execution prefix, machine record representation and updated stamp history.
  The source list is exactly the raw cell list, including its leading zero;
  there is no sorting or deduplication. The full `PathResult` agrees, including
  any existing mixed line/object hits.

**Boundary:** `lineCell` is a proof-local restatement of the inner line loop at
flags 3, following the existing object-cell proof approach. Its geometry and
append operations are the production functions, but this theorem is not yet
an equality for the actual enclosing `Scene.pathTraverse`. No claim is made
that future edits to the runtime loop automatically invalidate this fragment's
proof. Connecting the runtime definition, block logging and grid iteration
remains necessary. Successful fractions, initial machine/scene encodings,
separation, stamp representation and a sufficient candidate reserve remain
explicit hypotheses. The join adds a source scene lookup relation; it does not
assume a desired output or a fact at a reached callback.

Validation: `scripts/verify_e1m1_line_source.py` extends the existing pinned-byte
certificate and strict transitive axiom audit. `tests/test_e1m1_line_source.py`
checks dropped flags/history/capacity/lookup assumptions and changed machine
entry, plus concrete kernel-checked duplicate ordering, lookup-before-skip,
rejected-line marking and full-buffer behavior. The prior mixed traversal
suite and broader proof build are rechecked; results are in
`artifacts/e1m1-line-source/validation.json`. Runtime and instruction semantics
remain unchanged; no independent emulator cross-check is added here.

Next connect this fragment to the actual production outer loop and construct
the bounded itinerary from initialized grid state. Then join ordered intercept
processing and aim clipping. Keep general budget sufficiency and reachable-state
contracts explicit until they are proved.

## Mixed inside/outside traversal

`E1M1OutsideLine`, `E1M1OutsideCell` and `E1M1MixedCellWalk` extend the conditional
cell traversal to include out-of-map coordinates. This closes the missing
outside branch of the cell-execution induction used by the firing path. It does
not yet identify the full mixed collection model with production `pathTraverse`.

The line branch runs the actual enabled CALL, signed/dimension bounds tests,
success epilogue and RET, restoring SP and the saved EDI grid counter. Its
bound is 22 modeled instructions. The object branch runs the caller success
test, enabled CALL and original object bounds/return sequence, with bound 28.
Neither branch requires an out-of-map table entry, list or callback result.
Protected stack reads preserve the original records and mutable visit stamps.

The complete outside cell adds the existing caller success/grid-advance proof,
for a bound of 71 instructions. Its collection and visited history are unchanged;
its numeric state and next PC follow the original step, including stalls,
endpoint exits and the signed iteration-budget test. The same memory frame
preserves data for future inside cells.

The mixed itinerary theorem chooses between the existing complete inside-cell
proof and this outside-cell proof using production `pathCellInside`. Only inside
cells require static list/geometry contracts and initial payload/head images.
The induction carries every required future image through both branches and
uses one initial sum-of-candidates budget. Outside cells cost zero candidates,
but their instruction bound and numeric step remain in the composed execution.
The returned collection relation records unchanged results outside and checked
line results followed by production object-cell results inside.

`Follows`, `grid` and `stopPc` are reused unchanged. Therefore the existing
legal-counter length bound and exhausted-budget exit theorem apply directly to
the mixed itinerary. In particular, outside cells cannot evade the original
64-iteration limit by having no candidates. Admitted boundary crossings may
leave or re-enter the map without resetting records, history or capacity.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1MixedCellWalk
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_mixed_cell_walk test_e1m1_cell_walk
python3 scripts/verify_e1m1_mixed_cell_walk.py
```

Negative checks require actual map dimensions/coordinates, the outside branch,
real stack/return addresses, saved-counter/record protection and unchanged
collection history. They reject incorrect numeric/PC results, missing initial
images or aggregate budget, and understated instruction bounds. Kernel fixtures
exercise negative coordinates, both upper map boundaries, restored iterator
return PCs/SP, and the line counter; symbolic checks confirm that an outside
cell requires no payload/head and preserves its modeled result exactly.
Logs and the strict transitive audit are in `artifacts/e1m1-mixed-cell-walk/`.
The 29 authenticated ranges, 828 map cells, runtime and instruction semantics
are unchanged. No independent emulator rerun is claimed.

Actual itinerary construction, sufficient capacity for every reachable query,
initial encoding/layout/arithmetic discharge and production outer-line-loop
correspondence remain explicit obligations. Next connect the checked collection
to the production outer loop and construct the bounded itinerary from initialized
grid state. Ordered intercepts, clipping, full query returns/retries and complete
tic correspondence remain open.

## Finite in-map traversal composition

`E1M1CellWalkInvariant`, `E1M1CellWalk` and `E1M1CellWalkLimit` lift the generic
complete cell into a finite itinerary theorem. This discharges the repeated
in-map execution composition needed by the firing path, under explicit initial
images, static callback contracts and a sufficient total candidate budget.

The context bundles fixed pointers, map/scene values and static separation.
Each itinerary cell contains pure coordinates, its raw BLOCKMAP list, line data
and object nodes. `Images` requires the payload and selected object head for
all supplied cells in initial memory. `images_transport` carries the whole
family through the proved memory frame, so later cells receive their data from
execution. The dynamic state invariant carries caller SP, the map image, mixed
records and mutable visit history. Static record separation covers all 128
slots, including records appended in earlier cells.

`execution` inducts over the itinerary and repeatedly applies the actual cell
execution theorem. `Follows` relates each cell to the numeric grid step and
requires the original continuation PC before a nonempty tail. The last cell
may continue or exit. There is one input budget:

```text
incoming hit count + sum(line candidates + object candidates) <= 128
```

The induction derives each cell's room and the tail budget from actual collection
size bounds; it never resets capacity or assumes an intermediate memory image.
It produces one instruction prefix, the sum of per-cell instruction bounds,
per-cell production object results after checked line scans, composed visit
history, final numeric grid state/PC, protected reads and all initial cell images.

The limit lemmas use the real signed counter test. For a legal initial count
`n < 64`, `Follows` implies `cell_count <= 64 - n`; no length bound is assumed.
Exhausting that many cells implies the original exit PC, even when both axis
checks fail and the position stalls. Endpoint exits can happen sooner. The
proof explicitly excludes corrupt/negative initial counters from this bound.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1CellWalkLimit
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_cell_walk test_e1m1_cell_advance
python3 scripts/verify_e1m1_cell_walk.py
```

Checks reject dropped initial images, static protections, total capacity, route,
entry/control and counter assumptions; incorrect history/grid results and
understated instruction/iteration bounds also fail. Kernel-evaluated fixtures
exercise stalls, the 63-to-64 boundary, endpoint exit and a negative signed
counter. Logs and the strict transitive axiom audit are in
`artifacts/e1m1-cell-walk/`. The 29 DOS ranges, 828 map cells, runtime and modeled
instruction semantics remain unchanged. No new emulator comparison is claimed.

The theorem still takes an admitted in-map itinerary and sufficient aggregate
budget as inputs. It does not construct all real itineraries, prove the candidate
budget sufficient for all reachable queries. The mixed traversal above now
covers out-of-map cells. The collection relation records checked mixed line results followed by production
object-cell results; equality to the full production outer line loop is still
open. The next connection is from the collection model to that outer loop,
then ordering/clipping and remaining reachable-state
contracts. This is not complete aiming or a one-tic correspondence theorem.

## Reusable complete in-map cell

`E1M1CellLineBoundary`, `E1M1CellScanAdvance` and `E1M1CellAdvance` join the
previous reusable object phase to the complete generic line phase and actual
cell lookup. This discharges the in-map single-cell composition needed by the
firing path's bounded traversal. It constrains the original cell's execution,
mixed hit collection and numeric advance; the production object-cell function
is related to the result after the checked line scan.

The line boundary restores the caller view from SP and the saved EDI word.
EDI at scan entry is a temporary list cursor, so equating it directly to the
caller's grid counter would be wrong. At an actual lookup, the saved word comes
from the prologue and the recovered eleven-field observation equals the input
grid state. Line callbacks and the sentinel return preserve that observation
and every protected map, scene and selection word.

The scan-entry join executes all line candidates, transports persistent images,
derives object readiness/selection, runs the full object phase and advances the
grid. It updates the stamp/Boolean history and accounts for both lists with one
capacity premise. The gate join additionally derives the actual scan pointer,
callback and return word from the enabled BLOCKMAP lookup. Bounds are
`59 + 281 * line_count + 230 * object_count` from scan entry and
`89 + 281 * line_count + 230 * object_count` from the cell gate. The returned
PC is the original `nextPc`, including endpoint and iteration-limit decisions.

The output contains the exact numeric step, production object-cell hits applied
to the checked mixed line-scan result, updated visited history, persistent
map/scene/selection images and a protected-read frame. The final hit-count bound
supplies the conservative reserve
`128 - (incoming_hit_count + line_count + object_count)`. No scan-to-object
capacity refill or reached-state callback image is assumed.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1CellAdvance
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_cell_advance test_e1m1_cell_object_advance
python3 scripts/verify_e1m1_cell_advance.py
```

Negative checks cover saved-counter/stack views, callback/return slots, selected
cell and existing record protection, shared capacity, updated visit history,
scene selection, numeric/control results and instruction bounds. Logs and the
strict transitive axiom audit are in `artifacts/e1m1-cell-advance/`. The same
29 DOS ranges and 828 map cells are pinned. Runtime and instruction semantics
are unchanged; no new emulator comparison is claimed.

Initial memory images, static separation, callback arithmetic, selected scene
IDs and whole-cell capacity remain explicit. The line result is still the
checked mixed scan result, not a newly proved production outer-loop equality.
The finite in-map itinerary theorem above now supplies repeated-cell invariant
composition and budget propagation. The mixed traversal further supplies
outside cells. General budget sufficiency and the join to production collection
remain open. Intercept ordering,
aim clipping, complete query/tic and reachable-state discharge remain open.

## Reusable object phase and advance

`E1M1CellObjectSelection`, `E1M1CellObjectRun` and `E1M1CellObjectAdvance` compose
the object half of an arbitrary in-map cell, rather than specializing another
numbered cell in the firing prefix.

The selection image records the actual object-table pointer and selected cell
head. Its frame theorem allows that selection to travel with the previously
proved map and callback images. The real CALL/prologue preserve positive grid
locals and all four live grid registers, so the object lookup's caller view has
the original eleven-field numeric observation. The caller return word is derived
from the real CALL and survives the callback PUSH.

Starting from a successful line return, the generic execution theorem runs the
success test, enabled object CALL, bounds/table lookup, full empty or nonempty
list and epilogue. The persistent geometry/list image and actual freshly written
callback/return words provide iterator readiness. Mixed collection records,
numeric state, visited history and protected reads survive this phase. Its
instruction bound is `31 + 230 * object_count`.

The advance join adds the caller success test and original step, for a bound of
`52 + 230 * object_count`. It relates the collected result to the production
scene-cell function using the actual ID order and target relation. It retains
map, scene and selection images and visited history. The final hit-count bound
supplies a reserve of `128 - (incoming_hit_count + object_count)` under the
incoming capacity premise. Endpoint and iteration-limit control remain the
original `nextPc`, rather than assuming an unconditional next-cell gate.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1CellObjectAdvance
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_cell_object_advance test_e1m1_firing_next_scene
python3 scripts/verify_e1m1_cell_object_advance.py
```

Negative checks require real table/head selection, both store protections, the
caller stack and return word, geometry/layout, incoming capacity, scene ID order
and target relation. They reject incorrect numeric/control results, understated
instruction bounds and extra capacity. Logs and the strict transitive axiom audit
are in `artifacts/e1m1-cell-object-advance/`. The same 29 DOS ranges and 828 map
cells remain pinned; runtime and instruction semantics are unchanged.

This component has an explicit pre-object line-return contract. The complete
in-map cell theorem above now supplies it from the generic line phase, including
numeric/selection preservation and capacity. Repeated-cell induction remains open. Reachable-state input discharge,
later-cell capacity, full production outer-loop correspondence, intercept ordering,
aim clipping and a complete query/tic remain open. The initialized two-cell firing
prefix is unchanged; this step establishes a reusable component for the loop.

## Persistent callback data and readiness

`E1M1CellSceneInvariant`, `E1M1FiringSceneData` and `E1M1FiringNextScene` carry
callback geometry and object-list contents through the same cell frame as the map.
The persistent image separates initialized trace/active words, line geometry/back
flags, object geometry and links from temporary iterator stack words. Pure
contracts retain callback arithmetic, side separation and intercept/object layouts.

The first-cell preparation theorem works for an arbitrary future line/object
selection represented at firing entry. It derives initialized trace values and
retains the supplied line/object data through the actual first cell. The joined
two-cell theorem transports this image through both scans and advances, proving
it for the current selection and universally for any future selection meeting
those initial representation and protection contracts. This is not a claim that
all later selections already satisfy those contracts or that their scans execute.

Reusable line readiness derives callback geometry from the image, actual lookup
pointers, static layout and bounded IDs. The lookup readiness theorem obtains its
callback target from the actual line CALL/prologue, not a postulated stack word.
Reusable object readiness combines the persistent geometry/list with the actual
fresh object callback and caller-return words. Stack words are deliberately not
preserved as if later calls could not overwrite them.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextScene
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_firing_next_scene test_e1m1_firing_next_map
python3 scripts/verify_e1m1_firing_next_scene.py
```

Negative tests reject absent images, protected-read frames, layouts, actual lookup
pointers, bounded IDs, fresh callback/return words and initial future-selection
contracts. Logs and the strict transitive axiom audit are in
`artifacts/e1m1-firing-next-scene/`. The same 29 DOS ranges and 828 map cells are
pinned. Runtime and instruction semantics are unchanged.

The initialized two-cell numeric result, instruction bound, map image, mixed
intersections, visit history and conservative reserve remain unchanged. Arbitrary
cell object-head selection and complete cell execution still need composition;
repeated-cell induction, later-cell capacity and the production outer loop remain
open. Existing initial encodings, successful fractions, layouts, freshness and
candidate budget remain explicit. This does not complete aiming or a whole tic.

## Persistent map and lookup invariant

`E1M1CellMapInvariant`, `E1M1NextLookupFrame` and `E1M1FiringNextMap` connect the
map-data portion of the cell invariant to the actual initialized two-cell prefix.
The immutable image includes all raw 16-bit BLOCKMAP words, dimensions, map/line
pointers and initialized line/object option bits. A common protected-read frame
transports this image across component boundaries while keeping mutable stamps
and intersection records in their separate invariants.

The arbitrary-gate lookup theorem executes the original in-map lookup in at most
30 instructions. It retains the image and protected-read frame and carries mixed
records, their exact existing reserve and mutable visit history to the real line
scan entry. It does not manufacture a new reserve or assume callback results.
Gate PC, coordinates, selection and stack/record/stamp separation are explicit.

The firing join derives the protected-read relation from the completed first cell
through the second line scan, object lookup, full object list and advance. This
retains initialized values such as the traversal flags, rather than confusing them
with their pre-firing contents. The final map image is transported from the proved
first-cell image. The actual production line/object results also supply a bound on
the final hit count and therefore a reserve of
`128 - (first_line_count + first_object_count + next_tail_count + next_object_count)`.
No reached-state capacity hypothesis was added. The numeric state remains
`step (step initial)`, with the original `nextPc (step initial)`, and the continuous
instruction bound is unchanged.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextMap
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_firing_next_map test_e1m1_firing_next_numeric
python3 scripts/verify_e1m1_firing_next_map.py
```

Negative checks require the actual image/frame/layout, restored stack, protected
records/stamps and unchanged reserve, and reject wrong dimensions, control targets
and insufficient instruction bounds. Logs and the strict transitive axiom audit
are in `artifacts/e1m1-firing-next-map/`. The same 29 DOS ranges and 828 map cells
are pinned. Runtime and instruction semantics are unchanged.

The remaining loop obligations include callback geometry, dynamic object-list
images and layouts at arbitrary later cells, capacity across those cells and
production outer-loop correspondence. Existing initial encodings, successful
fractions, layout, freshness and total candidate budget remain premises. This is
not a proof of full aiming, a complete tic or audiovisual parity.

## Initialized second-cell numeric state

`E1M1NextScanGrid`, `E1M1NextLookupGrid` and `E1M1FiringNextNumeric` close the
numeric identification left open by the reusable object-to-grid boundary.
The second lookup's caller view now equals `step initial` in all eleven fields,
and the continuous prefix ends with `observe out = step (step initial)` and
`out.pc = nextPc (step initial)`.

The reusable scan lemmas preserve ECX, ESI and EBP and restore EDI from the
actual saved word. They preserve all seven positive grid locals using only
separation from the scan and following CALL/prologue. This matters for the
Y-intercept slot: the proof retains its updated value from the earlier advance,
without demanding separation from the store that updated it. The firing join
supplies saved words from actual CALL/PUSH execution and identifies the first
production collection result by determinism. It does not assume the reached
numeric equality.

The continuous prefix still preserves mixed records, updated visit stamps and
protected reads, with the unchanged bound
`526 + 281 * (first_line_count + next_tail_count) +
230 * (first_object_count + next_object_count)`.

Validation commands:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringNextNumeric
PYTHONPATH=scripts:tests python3 -m unittest -v test_e1m1_firing_next_numeric test_e1m1_firing_next_boundary
python3 scripts/verify_e1m1_firing_next_numeric.py
```

The certificate extends the same 29 authenticated DOS ranges and 828 map cells.
Tests reject incorrect saved slots, missing scan/CALL/heap separation, wrong
stack positions, reduced capacity, an unchanged numeric state, an unconditional
next-gate PC and an understated instruction bound. Logs and the strict transitive
axiom audit are in `artifacts/e1m1-firing-next-numeric/`. Runtime and instruction
semantics are unchanged.

This proves the initialized two-cell numeric prefix under the existing explicit
encoding, layout, freshness and capacity premises. It does not yet establish
repeated-cell invariant closure, later-cell capacity, the production outer loop,
intercept ordering, aim clipping or a complete query/tic.

## Complete initialized first-cell numeric state

`E1M1GridLocals` gives one protection contract for the seven stack-held locals
(endpoints, directions, strides and Y intercept). It derives separation from
all callback stack writes, even with wraparound/unaligned stacks. Its `Safe`
contract still explicitly requires separation from line stamps and the intercept
array/cursor; it contains addresses only, not local values or execution outcomes.
The endpoint lemma follows the stored path endpoints through both axis setups.

`E1M1FiringGridState` reuses protected reads through the complete line scan,
object lookup and object traversal. `before_observe` combines the resulting
seven local equalities with the four register facts into the full eleven-field
production-initialized grid state. `execution` rewrites the existing first
advance's numeric transition and next-PC theorem with that state, retaining the
continuous authenticated post-sound firing prefix and its existing bound.
`production_axis` connects the initialized axis fragment to the signed/wrapping
expression from `Path.pathTraverse`; the surrounding loop remains unproved.

This closes the previously open first-cell numeric initialization links. It
still depends on the post-sound inputs, successful arithmetic, map/scene/list
encodings, static separation (including the new local-versus-heap contract),
and candidate-count capacity. These assumptions require reachable-state
justification. It does not yet preserve the collected hit array across the
advance's local write, execute later cells, or establish traversal-wide capacity,
aim clipping, damage or complete query/tic/observable correspondence.

Recheck with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringGridState
python3 scripts/verify_e1m1_firing_grid_state.py
python3 -m unittest discover -s tests -p test_e1m1_firing_grid_state.py -v
```

The transitive certificate retains 29 authenticated code ranges and the 828-cell
map image. Tests reject missing heap separation, wrong endpoint slots, missing
register/local preservation, swapped axis initialization, incorrect execution
bounds and wrong result/exit claims. No runtime code or decoded instruction
semantics changed.

## Initialized grid registers through both scans

`OriginalLineInterceptRegister` carries the running X intercept (EBP) through
line-callback saves, side tests, rejection or insertion, callback restoration,
the mixed scan, and its sentinel epilogue. The existing stable scan invariant
protects the saved word; no additional reached-state value is assumed.
`E1M1ThingGridRegisters` carries EBP and EDI through every object callback,
the linked-list traversal and iterator exit. It reuses the list image/capacity
transport and callback saved-word frame theorems. The line iterator's EDI
restoration was already proved by `E1M1ScanReturn.parent_return`.

`E1M1FiringGridRegisters.before_advance` joins these preservation facts to
path initialization: at the first cell-step boundary EBP contains
`pathFirstIntercept p.x1 yout.2.1 yout.2.2` and EDI is zero. Its `execution`
theorem includes the existing authenticated firing prefix and numeric step
relation. The result either exits at the endpoint with count zero or reaches
the next-cell gate with count one. This supplies two more fields of the
initialized grid state without extra outcome premises. It does not yet
identify the reached endpoint/direction/stride/Y-intercept locals with their
initialized values, preserve the hit array across the step's local write,
or prove the surrounding source loop.

The input contracts still include initial memory and geometry, successful
arithmetic, static separation, a finite scene/list relation and
`line_count + object_count ≤ 128`. Reachability discharge, later cells and
traversal-wide capacity, aim clipping, damage and complete query/tic remain
open. No production runtime code or authenticated byte range changed.

Recheck this addition with:

```sh
./scripts/lake build Doom.Proofs.E1M1FiringGridRegisters
python3 scripts/verify_e1m1_firing_grid_registers.py
python3 -m unittest discover -s tests -p test_e1m1_firing_grid_registers.py -v
```

The verifier extends the preceding 29-range/828-cell certificate and strictly
audits every new theorem's transitive axioms. Negative tests cover wrong save
slots/registers, dropped list capacity/image premises, altered initialized
intercepts/counters, and incorrect counter or exit conclusions.

## First grid-advance instructions and numeric semantics

`OriginalPathAdvance` authenticates the next 72 bytes, `0x2cab5..0x2cafd`,
including both endpoint comparisons, both axis tests/updates, counter increment
and loop branch. Its execution theorem checks every path in at most 19 modeled
instructions. Endpoint equality exits before advancing or incrementing. X has
priority if both intercept tests match; a stall still increments the counter.
The last allowed iteration performs its update before the counter exit.

`E1M1PathAdvance` observes the numeric grid state, proves the exact resulting
state and next PC, and proves that the only write is to the Y-intercept local
on the X branch. The endpoint, direction and stride slots survive that write,
even on an unaligned or wrapping stack. `production_axis` identifies the axis
operations with an Int32/Fixed expression reproducing `Path.pathTraverse`'s
fragment, including signed right shifts and wrapping additions. The relationship
to the enclosing production loop remains open; this fragment theorem does not
silently assume the loop has been verified. `counter_limit` identifies the
signed machine comparison with the 64-iteration budget for indices `0..63`.

`E1M1ThingListFrame` lifts arbitrary protected-word preservation through the
whole finite object list and iterator return, using the existing per-visit frame
lemma and derived stack restoration. It provides the reusable memory part of
the remaining caller-state transport, without assuming per-node results.

`E1M1FiringAdvance.execution` joins the new block to either weapon's common
post-sound prefix and reaches either the next cell gate or the post-loop boundary
within `427 + 281 * line_candidate_count + 230 * object_count` instructions.
It proves the numeric step **relative to the reached observation**. The newer
`E1M1FiringGridRegisters` connection above supplies the initialized X intercept
and counter; the Y-intercept, stride, direction and endpoint locals remain open.
Both cell-coordinate registers were connected previously. No claim about
post-advance intercept-array preservation is added: separation from the new
local write must also be supplied before retaining that collection invariant.
Initial layout, encodings, finite-list/scene relations, arithmetic and capacity
contracts remain conditional; later cells and complete query/tic/observable
correspondence remain open.

Recheck with `python3 scripts/verify_e1m1_firing_advance.py` and
`PYTHONPATH=tests python3 -m unittest test_e1m1_firing_advance -v`.
For the independent instruction-level diagnostic, use
`.tools/x86-check/bin/python scripts/verify_e1m1_firing_advance.py --cross-check`.
The transitive certificate now checks 29 DOS code ranges and the same 828-cell
map image. Mutation tests reject changed bytes, file mappings and relocations,
incorrect bounds/PCs, swapped directions, off-by-one loop limits and missing
read separation. Kernel fixtures cover endpoint precedence, X priority, Y,
stalls, final-iteration updates, signed intercepts and wrapping stacks/additions.
The Unicorn diagnostic compares all eight registers, mapped data memory, ordered
writes, exact instruction count, PC and final ZF/SF/OF/CF across 1,024 cases.
This diagnostic tests the pinned block, not whole-game reachability or emulator
correctness. Artifacts are in `artifacts/e1m1-firing-advance/`. Runtime source is
unchanged.

## Next priority and stopping rule

The joined initial-state scan covers all line-callback outcomes, including
negative fractions and early termination. The actual grid caller, iterator
prologue, bounds check and lookup now supply
the scan cursor and list/pointer facts from a protected pre-call map image;
outside cells return through the caller success test without map assumptions.
The shared firing prefix derives the initial coordinates and enable flags.
Traversal initialization and both axis/intercept setups now transport the map
image, globals and separation from traversal entry; initialization also supplies
the empty collection and first-cell capacity at scan entry. Aim-query setup now also derives that traversal-entry map contract from the
query-entry memory and layout. Firing setters and bullet-slope setup now derive
that query-entry contract from the common post-sound firing state. Next connect
the initial contract to the loaded map and earlier sound preservation.
Query-entry shooter words, selected trigonometric samples and origins now derive
traversal geometry. Firing now supplies that query-entry geometry from the
same post-sound boundary as the map. Preserved line geometry and initialized
trace now supply the callback templates, and firing-entry stack/storage
contracts supply their intercept layout. The complete mixed-scan initial
contract and mutable-stamp layout are now assembled from generated candidates,
a protected-read set and static separation. They connect to scan execution and
the aiming scan's sentinel return. The common firing-entry wrapper now derives
the selected list cursor and saved callback word and joins the original setup
to the complete first-cell line scan. The caller return frame is now preserved
through that scan and its success test reaches the thing gate. The preserved
option word now enables the original CALL, which supplies the actual coordinate
registers, callback and return word and retains the collected intercepts. ECX/ESI
restoration through callbacks, the scan loop and its epilogue now identifies the
thing-call coordinates with the intended cell. The thing prologue, signed
bounds checks, first object-table lookup and empty-list return now join to that
prefix, preserving the collected line intercepts. The nonempty-head callback
CALL and prologue now join to that prefix, with saved list and return words;
the return-side list decision is separately proved. The diagonal endpoint
construction now matches the live object-intercept expression, and the existing
divline helper now proves both side results. Object/trace representation is
transported from firing entry and actual trace initialization through the scan
and callback. The fraction now reuses the proved intersection helper and the
continuous firing prefix reaches either rejection boundary or insertion with
the exact production optional fraction. The optional object append now preserves
the preceding line records under a derived mixed pointer resolver; callback RET
restores the saved object cursor and joins the next-link test. The reusable
finite-list induction and iterator epilogue now compose from the list-head seam,
with the collection matching the production object-cell loop. The whole-list
image/layout now derives from firing-entry data, the trace from initialization,
and the saved words from actual CALL/prologue stores. The selected scene cell
and its ID order are tied to the DOS list, and a shared candidate-count bound
supplies capacity before either scan runs. Both coordinate registers now survive
the object list and iterator return, and the real caller success test reaches
the grid-step boundary. The next cell-step instructions now have checked execution
and a numeric observation theorem, and join to the firing prefix. All eleven
initialized numeric fields now survive both scans, under the explicit
local-versus-heap layout contract. The step now preserves the hit array/cursor,
and the nonendpoint first cell reaches the next gate with a legal count. A
reusable arbitrary-cell contract connects advancement to the next lookup.
The actual firing prefix now supplies its map and enable facts through the first
scans and reaches that next lookup with hits intact. Its updated visited-set
relation is now joined, including the next leading-zero duplicate condition.
The leading duplicate is now executed and its exact suffix, visited history
and conservative first-cell reserve are joined. Callback geometry, initialized
trace/active values, callback address and storage layout now accompany the same
reached suffix. The mixed line/object invariant now executes the remaining
next-cell line candidates and sentinel, retaining all earlier records in order.
The restored caller observations, success test and enabled object CALL are
now joined, retaining hits and visit history. The intended next-cell coordinates
and object-table lookup are now derived too, including empty-list return and
nonempty head selection. The second list image and capacity now derive from
initial data, its head and ID order are tied to the production scene, and the
existing object traversal executes the entire list and returns with visited
history intact. Object traversal now preserves all grid fields relative to
the actual lookup caller view, and its caller success test/grid advance are
joined with hits, visits and protected reads intact. That view now equals the
initialized first advance across the preceding line scan: the continuous second
advance has all eleven fields of `step (step initial)` and the corresponding
original PC. The persistent BLOCKMAP image, dimensions, pointers and initialized
options now accompany that endpoint, along with a protected-read frame and a
proved remaining reserve from the actual two-cell collection bound. A reusable
arbitrary-gate lookup carries the image, records, reserve and visits to scan
entry. Callback geometry, initialized trace/active data, object links and
static layouts now accompany that boundary for any protected future selection
represented initially. Reusable readiness derives line templates from real lookup
pointers and rebuilds temporary stack words at iterator entry. The arbitrary
in-map object phase now executes actual table/head selection, full traversal,
caller success and numeric advance, retaining persistent images, mutable history
and a proved remaining reserve. The generic complete-cell theorem now supplies
that pre-object contract from the full line scan and derives scan entry from the
real cell gate/lookup. It retains the original numeric step, updated visits and
persistent images across both scans with a single shared capacity budget. The
mixed induction now includes original line/object bounds returns for outside
cells, retaining all initially supplied inside-cell images and unchanged outside
collection/history. It uses the same numeric step, final PC and legal counter
bound. The mixed line result now agrees with the collector inside the actual
production traversal, through `E1M1TraversalSource.live_aiming`. The admitted machine walk now agrees with executable source collection,
including block logs and object iteration, via `E1M1LoggedWalk.execution`.
`E1M1GeneratedWalk.execution` now generates that route from the numeric gate
state, discharges `Follows`, and proves the endpoint/budget loop reaches the
original DOS exit. `E1M1LiveWalk.execution` now joins that generated replay to the actual finite
Int32 loop exposed by `E1M1TraversalLoop.live_aiming`, including its complete
mutable result and error-preserving source equality. `E1M1QuerySource.initialized`
now supplies numeric state, empty collection and initial visits from query entry.
`E1M1QueryCollection.execution` now derives those images and the complete gate
invariant from entry memory, composing setup and the live-loop correspondence
into one execution. The original nearest-intercept scan now matches the live selector via
`E1M1MinimumScan.execution`; `E1M1InterceptGate.execution` now joins the distance
gate, with callback entry and post-callback branches proved separately. `E1M1TraversalEntry.execution` now joins query entry through collection and the
selector prologue/count setup. `E1M1QueryDispatch.execution` now continues through
the scan, distance cutoff and first indirect callback entry. `E1M1QueryCallback.execution`
now derives the callback target from entry memory and preserves full record
encoding, stack and return word at that exact state. `E1M1AimStop` now closes the
one-sided wall callback and parent stop branch, with first-hit/map-flag agreement
and prologue separation explicit. `E1M1AimOpening.from_callback` now extends the
two-sided branch through the real opening helper and signed gate.
`E1M1AimMapped` now derives the height image from callback-entry memory, and
`E1M1AimDistance.execution` continues through the distance product with both
operands derived from that same entry state. Map/record contracts still need
discharge from the earlier query state. The open-portal bounds, final window decision and callback return are now joined; next connect the source line-hit iteration, parent continuation and actor callback effects,
encoded sentinel replacement, the repeated selection loop and aim clipping;
join the enclosing aim-ray/firing caller as the query return is assembled. General
budget sufficiency and reachable-state contracts remain to be discharged. Derive the
dynamic table/head encoding and read separation from the reachable object-list
relation. Derive initial map encodings, successful crossing fractions, static
layout and initial visit freshness from the loaded map/reachable-state relation.
Check whether the conservative total candidate budget suffices for the concrete
caller before weakening or replacing it. Reuse the derived callback readiness,
frame and iteration-limit lemmas; do not add assumptions at reached callbacks.
The itinerary and production collection loop are now joined. Connect ordered
intercept processing next, reusing this exact final collection state. Then prove
the aim callback's portal/target clipping, including early-stop behavior and
preservation of the return frame needed by the proved query epilogue.
After autoaim, connect per-pellet RNG/damage. The preceding sound/event-order boundary
and preservation of this post-sound input relation remain open. After the firing
action returns, connect the later same-tic flash countdown and the event handler
to the existing production-tick proof. Sound samples remain outside the first
silent correspondence target; gameplay-visible sound-system effects and call
ordering cannot simply be assumed away.
The original `P_FireWeapon` proof covers earlier attack initiation and noise;
keep it distinct from `A_FirePistol`/`A_FireShotgun`. Ready/refire/lowering
recursive transitions also remain explicit obligations.

For each new proof, identify the one-tic obligation it discharges, the live
function it constrains, and the assumptions still needed by its caller. Prefer
joining existing components. Resume startup/allocator work only for a concrete
initialization or observable-memory fact needed by those joins. Do not count
axiom-audited declarations as progress toward whole-game equivalence.

## Recheck this connection

```sh
./scripts/lake build Doom.Proofs.E1M1WeaponRuntime Doom.Proofs.E1M1WeaponDischarge lean-doom doom-tests weapon-probe audio-probe
.lake/build/bin/doom-tests
PYTHONPATH=tests python3 -m unittest test_weapon_actions_proof test_e1m1_weapon_runtime test_e1m1_weapon_flash test_weapons -v
```

The runtime tests check the transitive theorem axioms against
`propext`, `Quot.sound`, and `Classical.choice`; reject dropped branch/representation
premises, a changed machine entry, and an unchanged-before-update observation;
and instantiate the bridge on the existing unaligned-player/wrapping-stack
shotgun-flash fixture. They also check that changing the production tic timing
breaks the context contract. Existing weapon tests exercise firing, selection,
flash/sound timing, ammo, restart, pellets and original C reference sequences.
These checks supplement the kernel proofs; they do not turn this branch into a
complete one-tic correspondence theorem.


## Selected blocking line outcomes

The next part of aiming package 2 connects both early line stops to the same
reached-selection interface used for open portals. Three additions are checked:

- `E1M1AimBlockingSource.wall` / `.closed`: the production source loop stops at
  an arbitrary selected iteration before clipping or division. Closed means
  `min ceilings ≤ max floors`, including equality.
- `E1M1AimClosedReturn.execution`: the original closed-opening branch runs from
  callback entry through the eight-instruction false-return epilogue and the
  four-instruction parent branch, reaching 0x2c88c in at most 60 instructions.
  Stack separation proves the real return address survives the helper. The
  existing one-sided 24-instruction path is transferred to the repeat program.
- `E1M1AimBlockingCycle.wall` / `.closed`: the selected original record determines
  the same source-path index through the history relation. Both implementations
  stop at that visit; lower and upper aim bounds are unchanged.
  The canonical source suffix returns the path stopped at `seen.length + 1`.

These proofs use the same decoded binary program as the continuing-portal proof.
No additional executable bytes or machine semantics were introduced. Closed
openings obtain map/stack/input facts from the persistent catalog and layout.
One-sided walls retain explicit map-flag and separation premises, rather than
pretending that the partial two-sided catalog already represents walls.

Remaining package-2 work: preserve a wall representation across continuing
callbacks, classify represented line outcomes under one interface, and compose
the blocking endings with finite prefixes. The actor branch and complete mixed
loop remain later work. This is not full `P_AimLineAttack` correspondence, much
less unrestricted E1M1 graphical or audio equivalence.

Evidence: `artifacts/e1m1-aim-blocking-cycle/validation.json`. Mutation checks
remove map/layout/selection premises and alter PCs, stack restoration, instruction
bounds, visit counts, and unchanged clipping bounds. An equality-height check
protects the inclusive closed-opening boundary. Prior portal-prefix tests and the
full proof target build are included. Existing emulator evidence is inherited;
runtime behavior and all prior Doom proof sources are unchanged.


## Whole-prefix blocking endings

Aiming package 2 now connects a finite sequence of continuing portals to either
a one-sided wall or a closed two-sided opening, using the actual reached state.

- `E1M1AimWallCatalog` records original-index wall membership, line kind,
  protection of the flags word, and the cleared two-sided bit. It needs no back
  sector. The existing cycle frame preserves every listed wall's byte and its
  separation conditions across callback writes, record marking and the next
  scan/CALL. Selected-entry inputs follow from the existing `Selection` relation.
- `E1M1AimPortalCarry.execution` generalizes prefix induction with a property of
  machine memory/state and its frame-preservation proof. The admitted final
  source selection ensures intermediate boundaries are callbacks, allowing
  stack-relative separation to transfer. Final selection, persistent invariant,
  carried property, bounds, visit history and source-suffix equality are derived.
  This is reusable for later protected data; it does not assume the desired
  correspondence conclusion or any intermediate callback state.
- `E1M1AimBlockingPrefix.wall` carries the initial wall catalog and executes the
  final wall callback. `.closed` composes the existing prefix with the closed
  opening callback. Both reach 0x2c88c and the canonical source result at
  `seen.length + count + 1`, retaining the final portal bounds. The stopping
  visit is distinct from the `count` consumed prefix records. Instruction bounds
  are `count * (157 + 7 * initial.size) + 24` and the same prefix bound plus 60.

No wall facts, selected record or persistent invariant are supplied at the
reached ending. The initial wall/portal representations, source prefix
certificate and final source branch remain premises. Unified line dispatch is
still needed to combine open, closed and wall branches under one interface;
actors and the full mixed loop remain later work. Whole-call initialization,
return/controller connections and reachable-state premise discharge are not
completed by this result.

Evidence: `artifacts/e1m1-aim-blocking-prefix/validation.json`. Mutation checks
exercise frame/stack/pointer protection, catalog membership and representation,
initial carry and preservation hypotheses, admitted endpoint selection, exact
stop PC, bounds, visit count and instruction bounds. Prior blocking-cycle tests
and the full proof build are included. Prior Doom sources and runtime behavior
are unchanged; existing emulator evidence is inherited, not rerun.


## Unified selected-line dispatch

The local line-outcome interface for aiming package 2 is now unified:

- `E1M1AimLineDispatch.dispatch` computes an outcome from the source flags,
  back sector, signed opening and clipped window. Wall and closed-sector stops
  retain the entering bounds; an open portal may stop with new clipped bounds
  or continue and log its portal. A missing back sector yields no supported
  decision, matching the production branch's explicit unverified-data error.
- `E1M1AimLineCoverage.Coverage` requires each original line intercept to have a
  wall or two-sided catalog entry. `selected` derives membership for the reached
  callback from its original-buffer identity. `exclusive` proves shared source
  representation cannot classify the same entry as both wall and portal.
  Actors are outside this line-only obligation; complete E1M1 coverage is still
  a premise, not a consequence of the theorem.
- `E1M1AimLineCycle.execution` dispatches all four outcomes with one shared
  selected-callback contract. It combines actual decoded DOS instruction
  prefixes, exact stop PC, canonical source suffix, clipped bounds, consumed
  history and aligned next boundary. On continuation it preserves the wall
  catalog at any reached selected callback, using the already proved frame.
  No wall/open/closed/window outcome is supplied as a hypothesis. Successful
  division facts remain guarded by an open sector and differing heights.

The result has a uniform bound of `157 + 7 * work.size`. A stopping hit returns
source `stopped path (seen.length + 1)` at DOS PC 0x2c88c. A continuing hit consumes
exactly the selected record, appends its portal and processes the canonical next
source index. The existing whole-prefix ending theorems remain available.

Next is package 3's actor-hit path, followed by package 4's complete mixed loop.
The result does not discharge arbitrary reachable input representation or numeric
premises and does not complete the whole aiming call, autoaim controller, or
whole-game audiovisual correspondence.

Evidence: `artifacts/e1m1-aim-line-cycle/validation.json`. Tests remove coverage,
selection, catalog/source representation and guarded arithmetic premises, and
mutate stop PC, visit count, bounds, history, portal log and preserved wall set.
Kernel examples cover wall priority, missing back sectors, equality closing the
sector or aim window, both floor/ceiling clipping and signed negative heights.
Those examples exercise classifier boundaries; binary/source correspondence is
provided by the generic kernel-checked theorem. Prior prefix regressions and the
full proof build pass. No runtime, decoder, semantics or prior Doom proof changes;
previous emulator evidence is inherited rather than rerun.


## Actor rejection and traversal marking

Aiming package 3 starts with the non-line callback's early skips. The newly
pinned range 0x2b81a–0x2b843 (exclusive end) loads the shooter pointer, compares
it with the selected actor, and tests the actor's shootable flag if different.
Self-rejection jumps to the shared pop/RET epilogue; nonshootable rejection has
its own epilogue. Both return one, so the parent continues and marks the record.

- `OriginalAimActorGuard` proves decoding, pointer and flag decisions, and the
  two return sequences. Extraction checks original bytes, file mapping and the
  relocation to data-object offset 0x2b9ac. No instruction semantics were added.
- `E1M1AimActorSkip` includes the earlier repeat program unchanged, transports
  record/shooter/flag reads across the six-push prologue, executes the real RET
  and parent continuation, and proves the resulting memory is the saved-frame
  memory with the selected fraction sentinel stored. Self callbacks take 22
  instructions, nonshootable callbacks 23; with the parent they take 27/28.
  Saved EBX, ESI and EDI and the caller stack are restored for traversal reuse.
- `E1M1AimActorSkipJoin` proves the source skip at any selected iteration and
  preserves the entire intercept image through the prologue. At the reached
  selected callback, it derives the same rejected actor, consumed buffer/history,
  unchanged bounds and unchanged portal log, and source continuation at the
  next canonical index. The actual DOS destination is the scan head 0x2c83a.

The source/binary representation of actor pointer identity and shootability is
explicit, as are read separation, bounded buffer size and resolver stability.
This does not claim an actor catalog has been initialized or preserved through
arbitrary earlier callbacks. The next scan and returned aligned boundary still
need to be connected for this branch. Eligible actors then need top/bottom slope
computations, rejection tests, clipping, center slope and target stores. The
complete mixed traversal and full aiming call remain separate work packages.

Evidence: `artifacts/e1m1-aim-actor-skip/validation.json`. Strict inherited audit,
authentic byte/file-offset/relocation mutations, required-premise/output contract
mutations, prior line-dispatch regressions and the complete proof build are
checked. Fresh Unicorn checks run 384 original-byte cases (128 each of self,
nonshootable and eligible), verifying all registers, modeled flags, stack and
sentinel write order, exact instruction counts and unchanged aim bounds. Eligible
cases end at 0x2b843 and are not evidence for the later slope arithmetic. The
emulator requires execution outside the sandbox on this host; no new external
service or runtime engine change is involved.


## Actor skips through the next aligned boundary

The early actor rejection paths now execute beyond the parent mark. New module
`E1M1AimActorSkipCycle` derives the real cursor reload, restored counter/maximum
and caller stack, then reuses the proved repeat-head/minimum-scan/indirect-CALL
execution. It does not assume a fresh scan state or a successful next selection.
The continuous prefix costs at most `41 + 7 * work.size` instructions.

The three outcomes are explicit: exhaustion with the original wrapped counter,
a minimum beyond range at 0x2c887, or an admitted selected callback. The exhausted
machine state is based on the actor return, not the portal callback's different
state. Protected reads and aim bounds survive all scan outcomes; an admitted
callback regains the existing persistent portal invariant through the reusable
frame theorem. Original hit identity, consumed buffer history, callback slot,
stack layout and query data are carried rather than assumed anew.

`E1M1AimActorSkipAligned` joins these outcomes to canonical source progress.
The source skips exactly the selected actor, preserving its bounds and portal
log; at an admitted successor both sides select the same hit at the next source
index. Its `line_boundary` theorem converts an admitted callback to the existing
line/portal interface, so earlier line proofs remain reusable after an actor
skip. Terminal actor states are deliberately not converted to portal states.

Remaining premises include the incoming persistent invariant and the selected
actor's pointer/shootability representation and prologue read separation. This
batch does not establish an actor catalog or preserve actor flags through all
callbacks, does not execute eligible-actor slope arithmetic, and does not prove
the whole mixed traversal or aiming call. Next priority is eligible actor
vertical slopes and the reject/clip/target branches, with actor representation
transport needed for later iteration.

Evidence: `artifacts/e1m1-aim-actor-cycle/validation.json`. The certificate includes
all prior authenticated ranges and their audit, plus the scan, aligned-cycle and
boundary-reuse contracts. Required-premise/output mutations and prior actor-skip
regressions accompany the complete proof build. There are no new binary ranges,
runtime changes or instruction semantics. Prior emulator evidence is inherited
without claiming an additional emulator run for this composition-only batch.


## Eligible actor top slope and first rejection

The eligible actor branch now reaches its first vertical decision. The new
50-byte range 0x2b843–0x2b875 loads the original query range and selected fraction,
performs the inlined fixed-point product, computes the wrapped actor-top minus
shooting-height numerator, calls the real FixedDiv, and compares its result with
the lower aim bound. Original bytes, file mapping and three global relocations
are authenticated. No decoder or instruction semantics were added.

- `OriginalAimActorTop` proves the call-site instructions, signed comparison and
  exact source operands, reusing the existing multiplication theorem.
- `E1M1AimActorTop` preserves the older program and runs the proved division
  implementation through its real stack writes and RET. Successful source
  `checkedPathDiv` discharges machine division safety; saturation is included.
  Protected reads survive the CALL and three helper pushes. The result proves
  the slope copies, retained actor pointer/distance, stack and unchanged bound.
- `E1M1AimActorTopEntry` derives eligibility and all arithmetic reads from the
  original callback-entry record and actor fields. The continuous prefix takes
  at most 56 modeled instructions. Its source rejection connection derives the
  same below-window decision for a represented production actor and advances
  the source suffix without a bottom-slope division or window/log changes.

Equality at the lower bound is admitted, including signed extremes. The prefix
ends before the rejection epilogue at 0x2b875 or before bottom-slope computation
at 0x2b881. Neither branch is executed further in this batch. Actor representation,
entry read separation and successful source arithmetic remain hypotheses, and
no all-reachable actor catalog is claimed. Next are the rejection return/scan
connection and bottom-slope computation, then clipping and final target stores.

Evidence: `artifacts/e1m1-aim-actor-top/validation.json`. The complete inherited
certificate/audit, new-byte/file-offset/relocation mutations, contract tests and
signed-edge examples accompany the proof build. Fresh Unicorn execution checks
384 original-byte cases: 288 normal and 96 saturated divisions, 135 below,
128 equal and 121 above the aim bound; negative and wrapped arithmetic and
wrapping stacks are included. These checks verify every register, modeled CMP
flags, actual division RET, ordered stack writes and protected memory. Emulator
checks are supporting finite evidence, not the universal theorem. No game code,
previous proof source, decoder or instruction semantics changed.


## Eligible actor top rejection through the next scan

The first eligible actor rejection now has a continuous original-byte execution
from callback entry to the next callback or terminal scan boundary. This closes
the return/parent/scan gap documented in the preceding milestone.

- `OriginalAimActorReject` authenticates the 12-byte true-return epilogue.
- `E1M1AimActorReject` proves that all six saved registers and the caller's return
  word survive FixedDiv. The epilogue restores them, returns true, and the parent
  marks exactly the selected fraction. The prefix from callback entry takes at
  most 69 modeled instructions.
- `E1M1AimActorRejectCycle.execution` derives the consumed record image and history,
  then reuses the existing complete minimum scan. The continuous bound is
  `82 + 7 * work.size`. It proves the exact exhaustion/range/callback alternatives,
  unchanged lower and upper aim bounds, matching one-hit source progress, protected
  reads, and the persistent traversal invariant at an admitted next callback.

These are conditional correspondence theorems, with source division success,
actor identity/shootability/height representation, query alignment and initial
layout/invariant premises. The proof does not presume a successful later callback
or a post-return memory image. Equal top/lower slopes still proceed to the
unproved bottom-slope branch; they are not admitted as strict top rejections.

The fresh emulator check runs 384 cases through actual original code, including
the real FixedDiv RET, actor RET, parent mark and indirect next CALL or scan exit.
It checks all eight registers, modeled flags, ordered memory writes, consumed
records and protected words, with saturated arithmetic, minimum ties, wrapping
stacks and the full 128-record capacity. This finite check supports the formal
proof; it is not a universal equivalence claim.

Evidence: `artifacts/e1m1-aim-actor-reject/validation.json`, the generated inherited
certificate and strict axiom audit, authenticated byte extraction, 17 contract
and previous-top regressions, and the complete proof build. Prior Doom sources,
production behavior, decoder and instruction semantics are unchanged.

Next: the actor bottom slope and its upper-window rejection; then clipping and
selection. Actor representation catalogs, complete mixed-loop composition and
whole aiming correspondence remain open.


## Actor bottom slope and restored rejection

The admitted-top branch now computes and compares the bottom slope using the
actual original instructions and actual FixedDiv CALL/RET. The extra authenticated
range is 0x2b881–0x2b89d (28 bytes); its two data relocations read shoot height and
the current upper aim bound. The following true-return epilogue was already
proved for line continuation and is reused here.

- `OriginalAimActorBottom` proves the wrapped bottom numerator, reused distance,
  call-site instructions and signed comparison. It does not add actor height to
  the bottom numerator. Equality with the upper bound proceeds to selection.
- `E1M1AimActorBottom.execution` proves the second division/decision in at most
  33 instructions, including saturation behavior, preservation of ESI/EDI's top
  slope, and EBX's transition from distance to upper bound.
- `E1M1AimActorBottomEntry.execution` starts at the actual callback entry and joins
  both divisions in at most 89 instructions. Entry read separation derives the
  second-stage operands and unchanged aim bounds across the first helper call.
- `E1M1AimActorBottomReject.execution` joins represented source actor fields,
  both successful source divisions, admitted top and strict bottom rejection to
  the actual callback return and parent mark, at most 102 instructions. Both
  divisions reuse four deeper stack slots; all six callback saves and the caller
  return word survive. The source loop advances exactly one hit, with unchanged
  window and portal log.

The proof remains conditional on representation, read separation and arithmetic
success. It does not assume a post-division state or replace either division
with a callee stub. It ends at the parent scan head for a rejected actor, or at
clipping/selection entry for an admitted bottom. The bottom-rejection next scan,
clipping/target selection, actor catalogs, complete mixed loop and complete
P_AimLineAttack remain open.

Evidence: `artifacts/e1m1-aim-actor-bottom/validation.json`; inherited byte-backed
certificate and strict axiom audit, contract mutation tests and prior top-rejection
regressions, full proof build, and fresh original-byte emulator cases. The latter
cover two normal divisions, two saturations, mixed normal/saturated divisions,
signed boundary equality, rejection, wrapping arithmetic and stacks. They check
all registers and modeled flags at both decisions, ordered stack/parent writes,
protected words and the consumed record. These finite checks support the universal
conditional Lean proofs; they do not establish whole-game equivalence.

Next: connect this rejection to the reusable next-scan interface, then prove
admitted-target clipping and slope/target selection.


## Actor selection and bottom-rejection scan

Aiming package 3 now connects both outcomes of the bottom-slope decision.
Rejected actors proceed through the actual return and parent marking into the
complete next scan. Admitted actors clip both slopes, calculate the midpoint
and store the selected target and aim slope. The selected stores correspond to
the actual Lean loop's result, including its stopped path and window evidence.

- `E1M1AimActorBottomCycle.execution` reuses the scan/history machinery to reach
  the next callback or exit in at most `115 + 7 * work.size` instructions. It
  derives the consumed history, preserved aim bounds, persistent traversal
  invariant and exact source suffix progress from incoming representation.
- `OriginalAimActorSelect` authenticates 41 bytes at 0x2b8a9–0x2b8d2 (exclusive
  end), with relocations for the lower bound, target and aim-slope globals. Its
  exact instruction proof includes both signed comparisons and ordered stores.
- `E1M1AimActorSelect` identifies the clipped bottom as signed maximum and the
  clipped top as signed minimum. It reuses `PlayerHeight.half_word` to identify
  the compiler's sign correction as division toward zero after wrapped Int32
  addition. Negative odd sums and overflow are covered, without assuming that
  mathematical unbounded addition fits in a word. Both top-slope copies are
  required because the original compares ESI but retains EDI when unclipped.
- `E1M1AimActorSelectEntry.selected` starts at the actual callback entry, executes
  both real divisions, and reaches the selected-target and slope stores in at
  most 103 instructions. The memory target represents the source actor ID, and
  the stored slope equals the production loop's result. The source loop stops
  at this hit and retains its exact path prefix and portal/window evidence.

These are universal conditional theorems. Actor identity/fields, arithmetic
success, admission, memory separation, and (for the cycle) source alignment and
incoming traversal representation remain explicit premises. Selection ends at
0x2b8d2, **before** the false-return epilogue; the source's stop is proved but the
machine's return and enclosing traversal stop are not yet connected here.
Actor catalogs, mixed-loop composition and whole aiming remain open.

Evidence: `artifacts/e1m1-aim-actor-select/validation.json`, inherited certificate
with strict axiom audit, byte/mapping/relocation authentication, contract mutation
and prior-bottom regression tests, and the full proof build. Fresh 384-case
original-byte emulator checks cover both real divisions and both outcomes:
rejected actors return, mark and scan to the next callback/exit; accepted actors
clip and store. Checks include all registers, modeled comparison/scan flags,
ordered writes, protected memory, ties, exhaustion, range exits, 128-record
buffers, wrapping stacks, negative odd midpoints and wrapped midpoint sums.
Final selection flags are unspecified by the model and are not claimed matched.
The finite checks supplement the proofs. Production behavior, instruction
semantics, decoder and prior Doom source files remain unchanged.

Next: connect selected-target return and enclosing traversal stop, then collect
the actor outcomes into the common catalog for mixed line/actor traversal.


## Selected actor return and aligned traversal stop

The successful actor branch now runs continuously from callback entry through
both divisions, clipping, midpoint, target/slope stores, the real false-return
epilogue, and the parent's stop branch. Its endpoint is 0x2c88c; the enclosing
traversal function's own epilogue is still outside this theorem.

- `E1M1AimActorReturn.execution` extends selection by the existing eight-instruction
  callback epilogue and four-instruction parent branch, for at most 115 instructions
  from callback entry. All six saved registers and the caller stack/return word
  are recovered after both divisions and the selection stores. EAX returns zero;
  the parent reloads its cursor and stops. No new binary range or instruction
  semantics is introduced: the already-authenticated false return is reused.
- `E1M1AimActorReturn.Safe` states the additional concrete separation obligation:
  both target/slope globals are disjoint from the six saved words and return word.
  `saved_slot` derives preservation; `safe_transfer` carries the obligation across
  earlier callbacks whenever their stack pointers agree. It is not assumed
  automatically from the earlier portal layout, which lacks these two globals.
- `E1M1AimActorStop.records` proves the entire bounded intercept buffer is preserved.
  The successful hit is not sentinel-marked, and no subsequent minimum scan runs
  in this prefix. The two selection globals are disjoint from all three words
  of every record at the full 128-entry capacity.
- `E1M1AimActorStop.execution` derives the current actor, source position, return
  address and query values from the actual selected-index/history boundary.
  It proves that the target/slope stores survive to the parent stop, both aim
  bounds survive, and the canonical production suffix returns the exact source
  target, stopped path, clipping window and portal evidence at this visited hit.

The result remains conditional on actor representation, source division success,
both admission decisions, source-query alignment and memory separation. It does
not establish those premises for every reachable game state. Actor catalogs,
composition of arbitrary line/actor sequences, the enclosing traversal return
and complete P_AimLineAttack correspondence remain open.

Evidence: `artifacts/e1m1-aim-actor-return/validation.json`, the inherited pinned
47-range certificate and strict axiom audit, contract mutation/prior-selection
regressions, and the full proof build. Fresh 384-case original-byte checks now
execute accepted actors through the actual callback RET and parent stop, checking
all six restored registers, EAX, ESP, cursor, modeled flags, unchanged hit buffer,
selected stores, exact ordered writes and instruction counts. Rejected actors
continue through their full next scan as a regression. Cases include wrapping
stacks, normal/saturated divisions, signed-boundary equality, negative odd and
overflowing midpoint sums. Intermediate selection flags remain unmodeled; the
false return resets flags before the parent test, whose modeled flags are checked.
The finite checks supplement the universal conditional Lean proofs.

Next: collect actor eligibility, top rejection, bottom rejection and selection
into a common actor catalog/interface, then compose with the line traversal.
Production behavior, decoder, instruction semantics and prior Doom sources are
unchanged.


## Unified actor dispatch and continuation interface

`E1M1AimActorCycle.execution` now covers all four actor outcomes in one theorem:
self/nonshootable skip, strict top rejection, strict bottom rejection, and selected
target. The source identity, flags and slope comparisons determine the outcome;
the caller does not supply a preselected branch. The theorem uses the same
byte-authenticated program and bounds execution by `115 + 7 * work.size`.

- `E1M1AimActorDispatch` exposes the source order. Ignored actors bypass both
  divisions; top-rejected actors bypass bottom division. The unified theorem's
  top-division premise is conditional on eligibility, and its bottom-division
  premise additionally requires top admission. Both signed equalities remain
  admitted. Actor memory/read-separation premises are still explicit inputs.
- `E1M1AimActorBoundary` normalizes all three continuing machine branches into
  one terminal-or-callback interface. Exhaustion and out-of-range cases prove
  the actual exit PC (0x2c887), finished source suffix and source path length.
  Live cases retain exact minimum/index selection, persistent traversal state,
  and the corresponding source visited hit. The old branch-specific terminal
  register images are not substituted for one another.
- `E1M1AimActorCycle.Outcome` retains consumed history and source progress for
  continuation, with unchanged bounds and portal log, a memory frame, and a
  transport theorem for selection-store/stack separation. Selection instead
  retains the unmarked buffer and the exact source target, slope, stopped path
  and window at the parent's stop (0x2c88c).
- `next_callback` recovers a specified admitted minimum from any of the three
  continuing outcomes; `line_boundary` then feeds that callback directly into
  the existing line/portal interface. This is the shared boundary needed for
  mixed traversal, not yet an induction over an arbitrary mixed sequence.

No actor representation catalog is assumed proved by this interface. Pointer
identity, flags, heights, read separation, source-query alignment, arithmetic
success on reached branches, and incoming persistent state remain obligations.
The unified theorem does not carry an actor catalog through previous callbacks
or establish its premises for all reachable E1M1 states. Enclosing traversal
returns, whole P_AimLineAttack and whole-game equivalence remain open.

Evidence: `artifacts/e1m1-aim-actor-dispatch/validation.json`, inherited 47-range
pinned certificate, strict axiom audit, contract mutation/prior-return regressions,
and complete proof build. Three existing original-byte suites are freshly run
(1,152 cases): ignored callbacks through the parent mark, top rejection through
the next scan, and both bottom outcomes through next scan or selected return/stop.
Their exact scopes are retained in the report. Universal dispatch and boundary
composition follow from the new Lean theorem; finite branch checks supplement it.
No new binary range, runtime behavior, decoder or instruction semantics changes;
all prior Doom source hashes remain unchanged.

Next: define and preserve the actor representation catalog, so this interface's
actor-specific premises can be obtained at each reached callback; then compose
the line and actor interfaces into the mixed traversal proof.


## Actor catalog and portal-prefix selection

`E1M1AimActorCatalog`, `E1M1AimActorCatalogCycle`, and
`E1M1AimActorPortalPrefix` connect actor representation to the existing callback
and portal-prefix proofs:

- `Catalog` describes every actor intercept in the immutable original collection:
  valid scene index, pointer/shooter identity, shootable bit, z and height. Its
  protected addresses cover stack writes, fraction marks, cursor stores and the
  next callback's CALL. `preserved` transports the entire catalog across the
  existing generic continuing frame. This includes actors not yet visited.
- `inputs` combines the catalog, selection/history and persistent traversal
  layout to derive the actor-specific machine premises. `execution` uses those
  facts for all four source-ordered actor outcomes and preserves the catalog at
  any successor callback. Conditional top/bottom division premises remain explicit.
- `selected` carries the catalog through an existing `Sequence` of continuing
  portals, then executes the selected actor callback, real return and parent stop
  at 0x2c88c. The final stores match the canonical source target and slope; source
  position advances by the portal count and the successful hit is not marked.
  The instruction bound is `count * (157 + 7 * initial.size) + 115`.

The prefix theorem reuses the existing generic `E1M1AimPortalCarry` induction.
It needs the actor catalog only at entry, rather than assuming actor fields and
separation again at the reached callback. Its premise is a proved continuing
portal sequence; it is not yet an arbitrary mixed line/actor traversal theorem.
Initial catalog establishment for reachable gameplay states, source alignment,
arithmetic success/admission, enclosing returns and whole aiming remain open.

Evidence: `artifacts/e1m1-aim-actor-catalog/validation.json`, the inherited pinned
47-range certificate, strict transitive axiom audit, positive/mutated contracts,
prior dispatch regressions and the complete proof build. Emulator branch evidence
is inherited from the previous milestone, not rerun or claimed as mixed-prefix
testing. No binary, runtime, decoder or instruction-semantics changes; prior Doom
source hashes remain unchanged.

Next: carry both line and actor representation through an arbitrary mixed
sequence, using the common successor boundary, then close traversal exits and
the enclosing aiming call. The catalog's initial reachable-state construction
remains a separate connection obligation.


## Mixed continuing traversal and selected hit

`E1M1AimMixedStep`, `E1M1AimMixedPrefix`, and `E1M1AimMixedSelected`
compose the continuing line and actor branches:

- `Step` describes a source portal crossing or a continuing actor outcome. The
  actor branch preserves conditional division evaluation and covers ignored,
  top-rejected and bottom-rejected actors. `execution` obtains a common aligned
  callback, both catalogs, source progress and final window/log from either kind.
  An admitted successor minimum rules out exhaustion during this step.
- `Sequence` selects each hit with the existing strict minimum scan and permits
  arbitrary interleavings of those branches. Its `execution` theorem constructs
  intermediate machine states and concatenates authenticated instruction prefixes.
  It requires only initial machine invariants and source branch conditions, not
  a next-state invariant or machine execution for each step. `capacity` bounds
  its length by the number of remaining distinct records.
- `selected` connects the mixed prefix to an admitted actor, its real callback
  return and the parent's stop at 0x2c88c. The final target/slope stores equal the
  canonical source answer at `seen.length + count`. The successful hit remains
  unmarked; the clipped window and accumulated portal log are retained.

The mixed-prefix instruction bound is `count * (157 + 7 * initial.size)`;
selection adds at most 115 instructions. Both line and actor catalog preservation
reuse the existing frame and cycle theorems. The line catalog is carried in
`Persistent`; the actor catalog is carried alongside it.

Scope: this is an induction over any supplied source sequence of continuing
hits that ends at an admitted callback. It does not yet establish that every
reachable aiming query has such a sequence or close mixed prefixes ending at
no-hit/range exhaustion or blocking walls/windows. Initial reachable-state
representation, the traversal epilogue and the enclosing aiming call remain open.

Evidence: `artifacts/e1m1-aim-mixed-traversal/validation.json`, inherited pinned
47-range authentication and strict transitive axiom audit, contract mutation
checks, an ignored-actor/portal composition example, prior catalog regressions
and the full proof build. Emulator evidence is inherited, not newly sampled.
No runtime, binary decoder or instruction-semantics changes; prior Doom source
hashes remain unchanged.

Next: extend the mixed induction to terminal no-hit/range and blocking outcomes,
then join its exits to the enclosing traversal/aiming return. Establishing the
initial catalogs and arithmetic conditions for reachable E1M1 states remains
an explicit obligation.


## Mixed traversal normal and blocking exits

`E1M1AimMixedBoundary`, `E1M1AimMixedExit`, and `E1M1AimMixedBlocking`
remove the admitted-final-hit restriction and connect the remaining stopping
branches to mixed prefixes:

- `from_line` retains the actual normal-exit PC when adapting the line boundary.
  The new one-step `execution` handles either continuing kind without requiring
  another admitted minimum; it returns a callback-or-exit boundary, the exact
  source suffix and a memory frame.
- `E1M1AimMixedExit.execution` inducts over the same source `Sequence` while
  carrying actor facts and an arbitrary frame-preserved property. `Ready` requires
  these facts only at live callbacks, where the stack has the callback shape.
  It does not claim that callback-layout predicates persist at a terminal PC.
  `completed` connects buffer exhaustion or a minimum fraction strictly beyond
  65536 to PC 0x2c887 and the canonical source no-target result.
- `closed`, `stopped`, and `wall` compose mixed prefixes with closed sector
  openings, clipped-window closure and represented walls respectively. They reach
  PC 0x2c88c and the source path stopped at `seen.length + count + 1`. The stopping
  hit is included in the source result without a new consumed-history entry.
  The wall theorem instantiates generic transport with the existing wall catalog.

The normal-exit prefix bound stays `count * (157 + 7 * initial.size)`. Closed
sector and wall stops add at most 60 and exactly 24 instructions, respectively;
window closure uses the existing one-cycle bound. Window outputs are the clipped
values for window closure, and unchanged values for wall/closed-sector stops.

These are conditional composition theorems, not a total query theorem. We still
need complete branch classification/sequence construction from reachable source
conditions, initial representation, the traversal epilogue and the enclosing
P_AimLineAttack return. The normal exit theorem begins with an already established
callback-or-exit boundary; it does not prove initial empty-buffer setup.

Evidence: `artifacts/e1m1-aim-mixed-exit/validation.json`, inherited pinned 47-range
authentication, strict transitive axiom audit, positive/mutated contracts, prior
mixed-prefix regressions and the full proof build. Emulator evidence is inherited.
No runtime, binary decoder or instruction-semantics changes; prior Doom source
hashes remain unchanged.

Next: combine the admitted-hit and terminal results behind one exhaustive source
outcome interface, and connect those real exit addresses to the traversal return.
Reachable initial-state and arithmetic obligations remain explicit.


## Exhaustive ordered-hit loop and termination

`E1M1AimHitOutcome`, `E1M1AimOrderedLoop`, and `E1M1AimOrderedResult`
advance checklist item 3 beyond the earlier conditional sequence composition:

- `Arithmetic` contains slope values and source division equations, guarded by
  the branches that evaluate them. `E1M1AimHitOutcome.execution` dispatches on
  the actual line/actor tag and source comparisons, deriving either a final
  result or a continuing callback with one consumed record. Line coverage rules
  out a missing represented back sector. No branch decision is a premise.
- `E1M1AimOrderedLoop.execution` uses strong induction on
  `initial.size - seen.length`. Every continuation consumes a fresh record, so
  the measure strictly decreases. Catalogs and persistent layout are recovered
  at each callback. Terminal states use the actual normal-exit PC. The theorem
  requires neither a supplied source `Sequence` nor a final selected hit/outcome.
- `E1M1AimOrderedResult.execution` specializes to the initial full buffer, empty
  visit/log history and initial aim bounds, then uses the existing `live` theorem
  to conclude equality with production `E1M1AimSource.afterPath`. It covers an
  empty collection only when the initial exit boundary has already been proved.

`Exit` records the real normal/stop PC and, for every source target, the matching
original-buffer identity and exact DOS target/slope stores. Source equality also
retains the final path and optional window. Zero slope is not mistaken for no
target. The instruction bound is `remaining * (157 + 7 * initial.size)`; at entry,
`remaining = initial.size`. This is an instruction-prefix result ending at
0x2c887 or 0x2c88c, before the enclosing traversal epilogue.

Explicit limitations: `Available` quantifies division availability over admitted
buffer histories/windows. This is a uniform source arithmetic premise, stronger
than availability only on an actual reachable trace. It supplies no machine
execution or outcome, but it still must be discharged or replaced by a suitable
reachable-state invariant. Initial boundary/catalog establishment and map
coverage remain premises. No-target global clearing/preservation is deliberately
absent from `Exit`: a no-target source answer plus an exit PC does not prove a
zero DOS target pointer or return slope. The complete P_AimLineAttack return and
whole-game equivalence remain unproved.

Evidence: `artifacts/e1m1-aim-ordered-loop/validation.json`, inherited pinned
47-range authentication, strict transitive axiom audit, contract mutations,
zero-slope selected-target checks, ignored-shooter short-circuit checks, explicit
no-target scope checks, prior mixed-exit regressions and the full proof build.
Emulator evidence is inherited. No runtime, decoder or instruction-semantics
changes; prior Doom source hashes remain unchanged.

Next: preserve/establish the no-target globals and the state needed by the
traversal epilogue, then join the real exits to the enclosing return. This moves
toward checklist item 4; reachable initialization/arithmetic remain item 6 work.


## Null-target preservation and return-value selection

`E1M1AimNoTargetFrame`, `E1M1AimLineFrameCycle`, `E1M1AimHitMemory`, and
`E1M1AimOrderedMemory` close the ordered-loop no-target memory gap:

- The wall and closed-opening executions now retain a generic word frame, using
  the actual prologue/helper memory updates. The unified line cycle exposes a
  frame on every branch, including clipped-window closure, so no terminal frame
  is assumed as a postcondition.
- The exhaustive hit theorem assumes a null target and protection of that word
  at entry. A stopping line retains nullness. Continuing line/actor callbacks
  retain their frame; successful actors still write the exact selected pointer
  and center slope. `Exit` now additionally relates a no-target source result to
  a null DOS pointer and a zero source slope.
- The bounded ordered-loop induction carries the protected target word at live
  callbacks and nullness at both live and terminal boundaries. The initial wrapper
  concludes the production `afterPath` result with this stronger memory relation.
- `no_target_value` proves the original `chosen` return expression yields zero
  when the pointer is null, without requiring the DOS slope global to be zero.
  `return_value` proves equality with the source slope for all outcomes, assuming
  represented pointers are non-null. This retains zero-slope selected targets.

Original DOOM clears the target pointer at setup; it need not clear the slope
word. `OriginalAimSetup.stored_target` already proves the local clearing store.
This milestone assumes nullness and `StableWord` protection at the ordered-loop
entry; joining setup and collection to those premises remains open. The
`return_value` theorem evaluates the existing return expression in the reached
memory. It does not execute either enclosing epilogue or prove saved-register,
stack or return-address obligations. Those are the next connections toward item 4.

Unchanged assumptions: represented map/object memory, line coverage, source
alignment, and uniform arithmetic availability over admitted histories/windows.
Non-null resolver pointers are explicit for the all-outcomes return-value theorem.
These are not yet established for every reachable E1M1 call.

Evidence: `artifacts/e1m1-aim-ordered-memory/validation.json`, inherited pinned
47-range authentication and strict transitive axiom audit, contract mutation
checks for initial nullness/protection and pointer non-nullness, stale-slope
no-target checks, prior ordered-loop regressions, and the full proof build.
Emulator evidence is inherited. No runtime, decoder or instruction-semantics
changes; prior Doom source hashes remain unchanged.

Next: carry the saved state needed by the real traversal epilogue, execute that
return, and join the existing aiming-return proof using the established target
and return-value relation. Setup/collection and reachable-state obligations remain
explicit.


### Real traversal return and parent cleanup

`OriginalTraversalReturn` authenticates and executes DOS bytes `0x2c887–0x2c899`
and `0x2cb0b–0x2cb10`. Exhaustion/range exit first sets EAX to one; callback stop
retains the callback result. Both paths write ECX to the traversal-cursor global,
discard the callback slot, pop EDI/ESI/ECX/EBX and execute the actual return.
The parent then discards its 48-byte local area and pops EBP/EDI/ESI.

`E1M1AimTraversalReturn` links these bytes with the existing full callback program
without changing any earlier source. It proves:

- A continuous 11- or 12-instruction prefix to `0x2cb11`, provided the saved
  return address at exit ESP+20 is `0x2cb0b` and is disjoint from the cursor store.
- The exact final cursor write, ESP advance of 84 bytes, and restored register
  words. Under explicit byte separation, the saved values equal the pre-return
  words even for unaligned/wrapping addresses. The next return address is at the
  original ESP+84; its relation to `0x2bbff` is a separate checked contract.
- The target and slope globals survive. The original aim-return expression still
  equals the source answer under the earlier exit relation and non-null resolver
  premise. This does **not** say EAX already holds that slope: it is still the
  traversal boolean until the outer aiming epilogue runs.
- Any already proved ordered-loop prefix can be extended by this return segment,
  with the endpoint saved-stack obligations visible in the theorem signature.

The two new ranges raise this certificate's authenticated set to 49. Validation
is in `artifacts/e1m1-aim-traversal-return/validation.json`: 16 tests (8 new),
1,396 audited declarations, and 585 full proof build jobs. The 211 previously
recorded Doom source hashes remain unchanged. Fresh Unicorn checks cover 256
combined executions with both branches, all general registers, every mapped data
byte, the exact cursor write, return PC, instruction count, unaligned/wrapping
stacks, and a stack overlapping the cursor global. Arithmetic flags remain
unknown where the existing interpreter models them that way. The emulator needs
JIT permission; it was run outside the filesystem sandbox after a sandboxed
engine initialization failed. Earlier emulator results remain inherited.

**Still open:** the current decoder does not recognize the parent's `RET 8` at
`0x2cb11`; this milestone stops before it. The saved return address and restored
register words are explicit endpoint premises, not facts yet derived through
every ordered-loop branch. Next, support and validate that real return form,
carry the saved caller frame through the loop, and join the existing aiming
return theorem. Setup/collection joins, uniform arithmetic availability and
reachable-state assumptions remain open. No complete `P_AimLineAttack`,
three-probe controller, or whole-game equivalence claim is made here.


### Complete aiming return chain

`Doom.Verification.X86ReturnCleanup` adds opt-in 32-bit near `RET imm16` support.
The decoder reads an unsigned little-endian immediate; execution reads the
return destination from the original ESP, then advances ESP by four plus that
unsigned immediate. Memory, flags and all other registers are preserved.
An instruction with zero cleanup matches the existing ordinary RET. A generic
prefix-lifting theorem preserves every old instruction, state and step count,
including code-memory jumps; no previous decoder/interpreter source was changed.
This uses the existing flat-address, successful-memory-access model, not a proof
of x86 segment/access-fault behavior or the DOS loader.

`OriginalPathReturn` authenticates `c2 08 00` at `0x2cb11` and proves its single
step. `E1M1AimCompletedReturn` links the old traversal program, that new step and
the existing original aiming epilogue. Its execution theorem gives a continuous
20/21-step prefix from the ordered-loop exit to the aiming caller. EAX now holds
the actual source slope (rather than just an unevaluated return expression),
under the earlier exit relation and non-null resolver premise. Both miss with
stale slope memory and a selected target with zero slope are covered.

The final stack advance is 116 bytes relative to loop-exit ESP. The final return
address comes from ESP+112; EBP/EDI/ESI/ECX are restored from ESP+96/+100/+104/+108.
The sole memory write is still the original traversal-cursor store. A caller-frame
theorem recovers those registers and the return destination from pre-return
memory under explicit byte separation. A composition theorem appends the entire
chain to existing ordered-loop prefixes, without replacing any intermediate state.

**Remaining assumptions:** return addresses at loop-exit ESP+20 (`0x2cb0b`) and
ESP+84 (`0x2bbff`) and their separation from the cursor global. These are checked
endpoint contracts, not yet established by transporting the caller frame through
every line/actor branch and the ordered-loop induction. The next proof work is
that invariant, followed by the setup/collection join. Uniform arithmetic
availability, reachable map/object-memory assumptions, the complete three-probe
controller and whole E1M1 correspondence remain open. This milestone closes the
return segment, not the complete `P_AimLineAttack` call.

Evidence is in `artifacts/e1m1-aim-completed-return/validation.json`. The new
certificate re-authenticates the aim-return bytes and adds RET 8 to this chain,
for 51 ranges total; it audits 1,432 declarations. There are 18 regression tests
(10 new), 588 full proof build jobs, and 213 unchanged prior Doom source hashes.
Fresh emulator checks cover 256 complete return chains and 128 isolated RET
immediate cases: all general registers, all mapped data bytes, exact writes,
return destinations/counts, stale/zero slopes, unaligned/wrapping stacks,
cleanup immediates in `0..0x7fff`, and exact flag preservation for RET imm16.
Two **additional diagnostics, excluded from passing conformance counts**, found
that installed Unicorn 2.1.4 sign-extends `0x8000` and `0xffff`. The unsigned Lean
model is retained. This agrees with the correction described in the
[upstream QEMU RET/RETF patch](https://mail-archive.com/qemu-devel@nongnu.org/msg1234957.html).
The actual Doom immediate is 8 and is unaffected. Generic high-immediate
emulator conformance is therefore not claimed. Full-chain arithmetic flags
retain the old model's unknown abstraction. Only the pinned `RET 8` bytes are attributed to DOS; other immediate
encodings are synthetic instruction tests. Game runtime behavior is unchanged.


## Saved caller memory through the aiming loop

`E1M1AimSavedWords` extends protection to include the target and slope globals
written on actor selection, and proves an actual word frame for that branch.
`E1M1AimActorSavedCycle` and `E1M1AimHitSaved` carry the guarantee through every
actor and line outcome. `E1M1AimOrderedSaved` propagates a finite list of watched
addresses through the exhaustive loop, using the existing decreasing remaining-hit
budget. Continuing callbacks transport protection using their established stack
equality; stopping branches prove memory preservation directly. Terminal
boundaries do not silently acquire a stack-position assumption.

`E1M1AimSavedCaller` instantiates the image with offsets 16, 20, 84, 96, 100,
104, 108 and 112 from a fixed base. The two nested return-address contents are
now supplied from entry memory; the image proves their reached values. Appending
the real return chain preserves the source slope result and restores the caller
PC, EBP, EDI, ESI and ECX from entry memory, with final ESP = base + 116.
The saved EBX slot is included in the image, but the new restoration predicate
has no EBX field. The earlier complete-return semantics are reused unchanged.

This removes the need to assume saved-word contents at the reached exit. It
**does not remove the endpoint ESP = base premise**: existing terminal boundary
relations discarded that fact. Initial protection (including stack, scratch,
intercept-buffer, target and slope separation), initial return addresses,
catalogs, arithmetic availability and resolver validity remain explicit.
Collection/setup joining and reachable-state justification remain open.

Validation: `artifacts/e1m1-aim-saved-caller/validation.json`. The authenticated
certificate reuses the 51 pinned ranges and checks the loop and return programs
separately before composing their executions. The 216 earlier Doom sources are
frozen. No runtime or decoder changes; no new emulator run. The preceding 384
passing emulator checks and two separately recorded high-immediate discrepancies
remain inherited evidence, not new checks or a physical-hardware claim.

Next: strengthen the terminal scan and stopping-callback connections with their
actual stack position, carry that into the exhaustive loop exit, and discharge
the remaining endpoint stack premise in this caller-memory composition.


## Stack position through the common aiming scan

`E1M1AimScanStack` strengthens the actual minimum-scan dispatch and the
history-aware repeat head. Its `Position target base out` keeps both the PC and
ESP: terminal exhaustion/range exit retains `base`; an indirect callback reaches
`target` with `base - 4`. The destination is explicit because a generic indirect
call could name the exit address itself. Terminal recovery therefore requires
destination distinctness; the concrete aiming destination satisfies it.
The proof reuses the existing selection-register theorem's stack equality,
which the previous range-rejection interface discarded. Exhaustion retains the
original counter wrapping decrement; the next CALL uses the original push.

`E1M1AimActorScanStack` threads the strengthened history dispatch through scans
after skipped actors and both slope-rejection branches. `E1M1AimLineScanStack`
does the same after continuing open-line callbacks. These are post-callback scan
executions starting at each callback's proved return result, not yet new whole
callback-cycle theorems. Their carried position lemmas recover `0x2b760` from
incoming slot invariants and the existing callback/mark memory frames; no new
reached-memory destination premise is introduced.

`E1M1AimScanCaller` derives terminal ESP from that concrete scan shape and
composes the supplied loop/scan prefix, saved-word image and real return chain.
The returned EAX still equals the source slope and caller values come from entry
memory. The theorem replaces the separate endpoint ESP equality with a scan
position proof. This is a terminal-scan composition; it does not assert that
`E1M1AimOrderedSaved.initial` now produces this position for all mixed-hit paths.

Remaining connection: retain the stronger stack output through all enclosing
line/actor cycle outcomes (including locally proved stopping callbacks), strengthen
the terminal boundary, and carry it through the exhaustive loop induction. Then
use the result to discharge `E1M1AimSavedCaller.execution`'s ESP premise for the
whole loop. Initial collection/setup and reachable-state assumptions remain open.

Validation: `artifacts/e1m1-aim-scan-stack/validation.json`. The certificate
checks links to the inherited byte-authenticated repeat, skipped-actor, top/bottom
actor, combined-loop and completed-return programs. It audits all new declarations
and preserves all 221 preceding Doom source snapshots. Tests cover arbitrary
indirect destination collision, wrapping push arithmetic, entry contracts,
callback-slot protection and rejection of missing stack/image premises. No new
code ranges or emulator run; runtime and instruction semantics are unchanged.


## Complete ordered-hit loop through the aiming caller

This closes the saved-frame-through-loop connection left open by the preceding
scan-stack milestone. `E1M1AimStackShape.Shape base out` names a fixed parent base:
normal and callback-stop exits have ESP = base; a live callback has ESP = base - 4.
The separate PCs distinguish these cases. Arithmetic is the existing wrapping
32-bit word arithmetic, including a parent base of zero.

`E1M1AimSkippedStack`, `E1M1AimTopStack` and `E1M1AimBottomStack` append the
strengthened scans to their real preceding callback executions. `E1M1AimActorStack`
combines those branches with actual target selection, preserving both protected
caller words and the stack shape. Its catalog wrapper derives the per-actor
machine premises as before. `E1M1AimOpenStack`, `E1M1AimPortalStack` and
`E1M1AimSynchronizedStack` carry the same fact through the open-line arithmetic,
return and source-alignment layers. `E1M1AimLineStack` includes one-sided walls,
closed openings, clipped-shut windows and continuing openings.

`E1M1AimHitStack` unifies all outcomes without changing the original source
result relation. `E1M1AimOrderedStack` carries the stronger result through the
existing terminating induction on remaining hits. At live callbacks, the proved
stack shape identifies the same parent base; every hit supplies the shape for
the next boundary. Exhaustion, range rejection, stopping walls and selected actors
all yield ESP = base. Protected watched words remain equal to entry memory.
No future callback sequence or final stack position is supplied.

`E1M1AimOrderedCaller.execution` instantiates watched words with the saved caller
slots, obtains the actual full-loop execution, memory image and final ESP, then
appends the previously authenticated real return chain. The resulting machine
prefix starts at the initial callback/exit boundary and ends at the caller PC.
Final EAX equals the slope from production `E1M1AimSource.afterPath`. EBP, EDI,
ESI and ECX are restored from entry memory, final ESP is base + 116, and the total
step bound is `collected.size * (157 + 7 * collected.size) + 21`. Saved EBX memory
is preserved by the image; the existing `Restores` predicate still has no EBX
field. No new claim about additional caller registers is introduced.

The combined theorem has no endpoint-memory, endpoint-ESP, supplied execution
prefix or future branch-sequence premise. It **does** require entry shape and
saved return addresses, initial aligned collection/source path, catalogs,
protection, target nullness, non-null resolver and uniform arithmetic availability.
It starts after collection; it is not yet a complete `P_AimLineAttack` call.
Initialization/ray/collection joining and reachable E1M1 justification remain
separate. The subsequent three-probe controller still needs completed query
results in place of its assumptions.

Validation: `artifacts/e1m1-aim-ordered-caller/validation.json`. The certificate
retains all 51 authenticated ranges and audits every new declaration and program
link. Regressions reject missing entry shape, word protection, actual branch
guards, source representations, finite budget and caller-address conditions,
and wrong final stack/EAX claims. All 225 preceding Doom sources are frozen.
No runtime or instruction-semantics change and no new emulator run.

Next: inventory the existing setup/collection exit contracts against this final
phase's entry contract, and prove the missing preservation at that seam. Prefer
joining existing executions and invariants over re-proving local aiming logic.


## Query collection through the first ordered aiming hit

`E1M1ScanInterface.dispatch` generalizes the established register/stack/frame
scan proof over a program with explicitly matching selection and CALL
instructions. This lets it operate inside the existing authenticated
`E1M1FirstIntercept.program`, which already includes the collection execution.
No assumption that two differently linked programs are equal is introduced.

`E1M1AimEntryFrame` proves that the handoff creates return word `0x2cb0b` at
collection-exit ESP minus four, despite the subsequent five setup stores. The
address-disjointness argument includes 32-bit wraparound. Its word-preservation
rule combines setup with the cursor store and callback return-word push.

`E1M1AimFirstSelection.execution` starts at `0x2cafd` with the actual collection
buffer, cursor and static protection. It executes setup and the first scan in
at most `32 + 7 * hits.size` instructions. Empty input exits with the authentic
wrapped ESI; an out-of-range minimum exits; an admitted minimum yields the exact
`E1M1HistoryDispatch.Selection hits hits []` with original records, pointer,
counter and range. The parent stack base is collection-exit ESP minus 24;
callbacks add a four-byte return word. The theorem derives stack shape and the
saved return at parent-base plus 20, and preserves every protected input word.

`E1M1AimQuerySelection.execution` composes that prefix with the existing complete
query initialization/collection theorem and its memory frame. Its only callback
value premise is in **query-entry memory**, at ESP plus eight. The earlier
`E1M1QueryCallback.aim_argument` supplies that value from original aim setup.
The resulting bound is `207 + bound(cells) + 7 * collected.size`, from query
entry `0x2c8a0` to callback entry or normal traversal exit. Source collection and
production `pathTraverse` equality remain in the result. The saved return and
stack/selection facts are not assumed at a reached state.

`E1M1AimFirstSelection.source` derives the same first source record from the
actual minimum selection, including strict tie ordering. Empty and range exits
leave the source result unchanged. Its empty-visitation and successful-source-
query hypotheses are still explicit; they have not been justified here for all
reachable calls.

This does not yet apply `E1M1AimOrderedCaller.execution` to the reached state.
The persistent catalogs, layout/protection, query globals and source boundary
must still be transported/assembled there. In particular, the repeat-loop
invariant's exhaustion form is tailored to a resumed callback; the initial
empty buffer must be connected without fabricating a prior callback execution.
The second nested return and other saved words can use the new protected-word
image, but their initial contents/protection still need the aiming-entry join.
Arithmetic availability and E1M1 reachability remain separate obligations.

Validation: `artifacts/e1m1-aim-query-selection/validation.json`, seven new
proof declarations and their authenticated contract wrappers, inherited strict
axiom audit, eight new regression tests plus the twelve preceding ordered-caller
tests, and the full proof build. All 237 preceding certificate-chain Doom
sources and all 621 pre-turn Doom sources are unchanged. No new byte ranges,
no emulator rerun, no runtime changes and no changes to instruction semantics.

Next: transport the persistent catalog/global/layout facts through the derived
word image, and form a first-entry boundary that joins the exhaustive hit loop
for all three initial outcomes without a fictional earlier callback.


## Initial loop entry and query-memory catalogs

`E1M1AimInitialBoundary.boundary` translates the first-scan outcome into the
common actor/line boundary. Empty and out-of-range input prove a terminal source
suffix; a live hit uses the already proved first-source-hit alignment and stack
shape. The origin parameter is the actual reached state's core, used only as a
stack anchor. There is no assumption that a prior callback or repeat head ran.
This resolves the initial-empty-buffer mismatch with the resumed-loop interface.

`E1M1AimInitialCaller.execution` applies the exhaustive terminating hit loop and
complete real aiming return to that boundary. Like the preceding ordered-caller
theorem, it returns the production `afterPath` slope and restores the caller from
entry memory. Unlike that theorem, it accepts the actual first-scan outcome and
has no supplied `AlignedNext` or origin parameter. Persistent facts are required
only for a live callback; no fictitious live invariant is needed for empty input.
The other catalog, global, saved-word, representation and arithmetic premises
remain explicit at this stage.

`E1M1AimEntryCatalog.Image` generalizes catalog transport over a protected-address
predicate. Its byte and halfword lemmas derive smaller reads from matching words.
Actor transport preserves shootability, z, height, shooter identity and future
callback protection. Wall transport preserves one-sided flags. Portal transport
preserves the flags, valid side halfword, both sector pointers and four heights.
Theorems transport every catalog entry, without assuming a selected prior hit,
mark index, previous callback run or new endpoint memory image.

`E1M1AimQueryCatalog.Protected` is exactly the conjunction of the three static
read guards in `E1M1AimQuerySelection.execution`'s word-preservation conclusion.
Its `image` theorem consumes that conclusion. `live_stack` derives callback ESP
from the actual first-scan outcome, distinguishing both terminal alternatives.
`catalogs` combines these results with the generic transports. Initial catalog
values are checked in query-entry memory; their static stack-separation fields
are checked using callback ESP = context SP minus 140. The `view` construction
only expresses this specification and is not a claimed executed state.

The `globals` theorem preserves range, eye height, initial bottom/top slopes and
null target using the same initial-to-reached memory image. Static protection
for those five addresses is explicit. These are value facts, not yet the entire
persistent callback invariant: callback-slot provenance, full layout/query
protection, record-slot separation and resolver stability still need assembly.
The second saved return and other caller values also need their initial-to-entry
connection. The query prefix and complete return program are not yet linked into
one execution theorem here. Source-query success/freshness and reachable E1M1
arithmetic/memory conditions remain separate obligations.

Validation: `artifacts/e1m1-aim-query-catalog/validation.json`. All thirteen new
proof declarations and their contract wrappers are audited; the completed-return
wrapper is linked to the inherited authenticated program. Nine new regressions
cover real empty entry without a live invariant, required instruction/data/stack
contracts, byte/halfword preservation, all catalog read sets, the memory-only
specification view and the five initial globals. The eight preceding first-query
selection tests are retained. All 241 earlier certificate-chain Doom sources
and all 625 pre-turn Doom sources are unchanged. No new byte ranges, semantics,
runtime behavior or emulator execution.

Next: derive and assemble the remaining persistent callback fields from the
initial layout and actual setup/scan memory effects, then apply the catalog and
global transports at that same first state and join the query/return programs.


## Derived first-callback persistent invariant

`E1M1AimFirstSlot.execution` strengthens the collection-exit setup/scan result
with the callback-slot value at collection-exit ESP minus 24. Setup writes the
loaded callback argument there. The minimum scan's cursor write and the final
CALL's adjacent return-word push preserve it, including wrapping stack
arithmetic. There is no assumption that this local slot contained that address
before setup. `E1M1AimQuerySlot.execution` retains the slot through the complete
query initialization/collection/first-selection prefix, alongside stack shape,
first saved return, source collection and protected-word image. Its callback
argument premise remains in query-entry memory.

`E1M1AimEntryPersistent.Initial` records only initial contracts: the callback's
static layout view, protection for the range/eye globals, clipping-global
separation, read-protected portal catalog, and range/eye values in initial
memory. It has no reached-state parameter, no callback-slot premise and no
resolver-stability premise.

`layout` transfers the static layout at equal ESP without marking a record.
`query_safe` uses the actual first selection to identify EBX and prove query
words separated from its bounded fraction mark. `slot_marks` derives protection
of the callback slot against all future fraction marks from the pre-existing
setup record guards. `resolver` proves that the real `E1M1ThingFinish.resolve`
ignores the changed fraction for both line and actor hits.

`persistent` assembles all ten fields of the live invariant. Stack equality is
derived from the first-scan outcome; portal and range/eye images come from the
query's initial-to-reached word frame. The callback slot comes from the new
setup/scan execution, rather than a presumed prior callback. Static separation
and representation are still checked against initial contracts.

`E1M1AimQueryPersistent.execution` applies this assembly to the exact endpoint
of `E1M1AimQuerySlot.execution`. The same continuous prefix now concludes
`out.pc = PTR_AimTraverse -> Persistent out ...`, with the original bound
`207 + bound(cells) + 7 * collected.size`. Empty and beyond-range branches retain
their genuine terminal outcomes. There is no supplied endpoint invariant,
register image, callback-slot value or execution prefix.

The initial contract is quantified over the result of the fixed **pure source
collection run**, not arbitrary machine endpoints or every arbitrary hit array.
The proved source-collection equality instantiates it. This is still conditional
on initial memory/layout correctness for that source collection; it does not
establish those conditions for every reachable E1M1 state. The source run's
result is also not being assumed equal to a chosen future machine state.

The all-actor/wall/global and saved-caller connections still need to be applied
to the same reached boundary, and the query and completed-return programs need
one verified linkage. This batch does not append the full hit loop and return
to the query prefix. Earlier aiming setup/ray, source success/fresh visitation,
initial caller data/protection and arithmetic/reachability remain separate.

Validation: `artifacts/e1m1-aim-query-persistent/validation.json`. All eight new
proof declarations and their contract wrappers are audited against the
inherited authenticated query program. Eight new tests cover created-slot
provenance, wrong slot/return addresses, required layout and current-record
protection, derived slot-mark separation, both resolver branches, required
initial contracts, and rejection of endpoint assumptions. The nine preceding
catalog/boundary tests remain included. All 245 preceding certificate-chain
Doom sources and all 629 pre-turn Doom sources are unchanged. No new byte
ranges, instruction semantics, runtime changes or emulator run.

Next: combine the remaining actor/wall/global and saved-caller entry facts at
this same endpoint, then link the query prefix with the already-proved complete
ordered-hit and return execution.


## Query-to-caller composition

`E1M1AimCallerCursor` separates return-chain requirements from callback write
protection. The complete return chain modifies the intercept cursor, so its
saved words need cursor separation; an empty query should not need a fictitious
live callback stack. `E1M1AimReadyCaller.execution` requests actor/wall catalogs,
target protection and watched-word protection only when the proved first-scan
outcome actually enters `0x2b760`. It still covers all terminal outcomes and
executes the original nested returns, including `RET 8`.

`E1M1AimQueryCaller.execution` applies the earlier transports at that exact
boundary. Its initial contract has only query-entry memory, static layout and
pure source collection data. It derives the live Persistent invariant,
actor/wall catalogs, target/saved-word guards, clipping bounds, zero target and
nested return address. Setup supplies its own created return word. The final
restoration theorem refers back to query-entry memory, not merely the
intermediate first-scan state.

The statement produces a query prefix and completed-loop/return prefix with
one identical middle state, plus a successful production `pathTraverse` result,
a successful `afterPath` result and equality of EAX with that result's slope.
The respective instruction bounds are
`207 + bound(cells) + 7 * collected.size` and
`collected.size * (157 + 7 * collected.size) + 21`.

This is a **two-program composition**, not yet a single-program execution.
The authenticated query map and authenticated completed-return map are each
explicit. Their overlap compatibility and common-map lifting are the immediate
next task. No reached state is assumed, but initial/source contracts still
require representation, coverage, successful all-true visitation, empty initial
visits, nonnull object pointers, arithmetic availability and protected initial
memory. Earlier aiming setup/ray and reachability remain open. Target-result
memory and controller composition are not strengthened by this slope theorem.

Validation: `artifacts/e1m1-aim-query-caller/validation.json`. Six new theorems
and their wrappers are audited with both inherited authenticated program maps.
Six new regression tests cover return cursor separation, both return addresses,
live-only callback contracts, query-entry restoration, the identical boundary,
correct EAX/source result, and rejection of missing initial/source contracts.
The eight preceding Persistent/slot tests are retained. All 249 previous
certificate-chain Doom sources and 633 pre-turn Doom sources remain unchanged.
No new instruction bytes, semantics, runtime changes or emulator run.


## Continuous query-to-caller execution

`E1M1AimProgramLink` closes the two-program gap. Compatibility means that at
any address either one map has no decoded instruction, or both maps have the
same operation **and length**. The maps share `E1M1PspriteLight.program` as their
inherited core. All 3,992 addresses in the additional regions are checked by
ordinary `decide`, split into 137 finite chunks; symbolic reductions cover the
unbounded complement. Both parts are kernel-checked proofs, not sampled emulator
runs or unchecked results from the Python scheduling helper.

The combined map gives the completed-return map priority and falls back to the
embedded query map. `contains_return` and `contains_query` prove that this choice
drops or changes neither map's decoded instructions. `append` lifts the original
query prefix to the existing RET-cleanup semantics, transfers both prefixes into
the union, and composes them without changing code memory, exit set, middle
state, or instruction count. Existing execution semantics remain unchanged.

`E1M1AimLinkedQuery.execution` now consumes the earlier initial-only contracts
and produces one continuous `X86ReturnCleanup.Prefix`, from `0x2c8a0` through the
complete ordered-hit loop and caller return. There is no middle-state,
compatibility or execution-prefix premise. Its bound is
`228 + bound(cells) + 7 * collected.size + collected.size * (157 + 7 * collected.size)`.
It retains equality with the actual source `pathTraverse` and `afterPath`
results, the returned slope in EAX and caller restoration from entry memory.
The certificate independently constructs the same union from the two inherited
authenticated maps and proves its equality with the production proof map.

This closes **single-map query-through-return linkage**, not all aiming.
Earlier `P_AimLineAttack` initialization/ray construction still needs to join this
entry. Source-query success and fresh visitation, initial memory/layout and
representation, pointer validity, arithmetic availability and reachable-state
preservation remain explicit. The combined endpoint theorem currently exposes
the slope and restored caller; target-presence transport and complete three-probe
controller composition still need their own endpoint connection.

Validation: `artifacts/e1m1-aim-linked-query/validation.json`. New tests reject
changed RET cleanup/length, dropped return instructions, mismatched middle
states, wrong instruction counts, wrong entry PC/EAX and missing initial
contracts. They also audit all new named declarations and the inherited
certificate chain. The preceding query/caller tests remain included. All 252
prior certificate-chain Doom sources and all 636 pre-turn Doom sources remain
unchanged. No new instruction bytes, emulator execution or runtime changes.

Next: carry the final target result through this same execution and connect the
earlier aim entry/ray setup, retaining the explicit source and reachability
obligations rather than assuming a complete `P_AimLineAttack` correspondence.


## Returned target and executed controller decision

`E1M1AimReturnedTarget.Image` retains the actual returned target word. No target
means that word is zero. A selected source ID has a witness in the collected
records whose resolved pointer equals the returned word; the target slope
global also matches. This deliberately does not infer that the witness is an
actor record or strengthen it to a direct object-pointer equality. The completed
return chain writes only the cursor, which is disjoint from these two globals.

`E1M1AimTargetCaller.execution` retains that image from the full ordered-hit
loop through the actual returns. `E1M1AimQueryTarget.execution` transports the
same initial contracts as the previous query theorem, joins the same machine
prefixes, and returns the image and `E1M1BulletAim.ProbeResult` for that endpoint.
Non-null record pointers and the returned EAX establish the controller interface;
it is no longer supplied as an independent endpoint assumption for this query.
The valid-target/zero-slope case is proved explicitly: zero EAX does not imply a
null target or a retry.

`E1M1AimTargetDecision.contains` proves that the unchanged linked program
contains the existing DOS controller instructions, including their lengths.
`decision` transfers the four-instruction slope store/target test into that map.
`execution` appends it to the continuous query. Its landing address is derived
from the restored PC and the return address at offset 112 in the initial caller
frame, not assumed of an existential reached state. The final bullet-slope word
at `0x2c0c0` matches the source slope. Target presence selects `0x2d81e`; absence
selects `0x2d7e4` after the center probe or `0x2d807` after the right probe.
The combined instruction bound is
`232 + bound(cells) + 7 * collected.size + collected.size * (157 + 7 * collected.size)`.

This connects the complete result interface and the actual decision for **one
probe**. It does not yet execute the retry setup, all three queries, or final
controller return. Earlier aim entry/ray setup and reachable-state justification
remain open. All initial source representation, successful visitation, fresh
visits, non-null pointer, arithmetic and protected-memory obligations are retained.

Validation: `artifacts/e1m1-aim-target-decision/validation.json`. Nine new proof
declarations and their wrappers receive the strict inherited axiom audit.
Seven new tests cover target/cursor separation, selected-record provenance,
non-null pointer encoding, returned EAX, the zero-slope hit, the actual decision
and stored slope, and the correct initial saved return slot. Five preceding
linked-query tests remain included. Mutations reject missing contracts, the
wrong endpoint, wrong branch/store addresses and the wrong saved return offset.
All 254 prior certificate-chain Doom sources and all 638 pre-turn Doom sources
remain unchanged. No new bytes, runtime changes, decoder changes, instruction
semantics changes or emulator rerun.

Next: connect the earlier aim entry and ray setup to this query boundary, then
use the derived probe interface to close the controller's retries. Initial and
reachable-state contracts remain explicit work, not consequences of this join.


## Aim-entry ray and production-query join

`E1M1AimSetupEntry.Inputs` describes pre-ray geometry/table samples, stack,
map memory, epoch, stamps and separation. `entry` derives every field of the
path-query entry contract at the actual setup result. In particular, the epoch
and fresh stamps are transported together; the callback, traversal flags and
nested return address come from executed stores. The address-only layout state
changes ESP and supplies no assumed post-execution memory contents.

`E1M1AimSetupCatalog.initial` fills the query contract's range, eye height,
clipping bounds, null target and nested return address from setup. `Remaining`
explicitly contains the catalog/read/protection obligations still needed at the
computed traversal boundary. It omits those generated values but does **not**
claim that all remaining fields have been transported from initial memory.
The independent payload and callback-protection premises also remain at that
boundary. Initial table/geometry encodings and fresh stamps are assumptions.

`E1M1AimSetupLink` proves the existing union agrees with the original ray,
setup and aim-epilogue decoders on their supported addresses (32 + 95 + 26 byte
positions, with symbolic exclusion elsewhere). It transfers the existing
11-instruction ray and 25-instruction setup proofs into the union. No new
instruction map, decoder rule or binary range is introduced.

`E1M1AimEntryQuery.execution` prepends those 36 instructions to the complete
query-through-return proof. It starts at `0x2bb80` and proves one continuous
execution, with bound
`264 + bound(cells) + 7 * collected.size + collected.size * (157 + 7 * collected.size)`.
The traversal coordinates are the actual shooter's position and its production
`attackEndpoint` for the same angle/range. With a positive range and a valid
shooter in `q.world`, `production` connects the derived path and processed
result to **`q.world.aimLineAttack shooter angle distance`**. The returned target
image and `ProbeResult` belong to that source result and the same machine
endpoint. Caller restoration is still expressed relative to the computed
traversal state; this theorem does not yet package every restored register as
an equality with its pre-ray value.

`return_address` proves the final caller slot is entry ESP and that its value
survives setup, under the stated read-protection condition. `decision` uses it
and the proved restoration to append the actual center/right target check and
slope store. Its execution starts at aim entry, uses the source target presence
for the final branch and has fixed bound term 268. The return destination is
an initial-memory condition, not an assumed reached-state PC.

This closes the **conditional aim-entry/ray/query/return composition**. It does
not establish reachable-state validity, execute every autoaim retry, or prove
whole-game parity. Source success, capacity, non-null pointer and arithmetic
contracts remain. The selected-target image still uses the collected-record
resolver; this is not a new direct actor-pointer identity theorem.

Validation: `artifacts/e1m1-aim-entry-query/validation.json`. Eleven new named
proofs and their wrappers receive the strict transitive axiom audit. Eight new
regression tests cover decoded CALL displacement/length, 36-instruction prefix,
entry geometry, callback/flag stores, generated query globals, saved return
protection/offset, production shooter/range conditions, the continuous endpoint
and explicit residual contracts. Seven preceding target-decision tests are
retained. All 258 prior certificate-chain Doom sources and 642 pre-turn Doom
sources remain unchanged. No runtime, decoder, instruction-semantic or binary
range changes; inherited emulator evidence was not rerun.

Next: transport the remaining traversal-boundary catalogs, payloads and callback
protection from pre-ray memory, then reuse this complete query interface across
the three-probe controller. Reachable E1M1 invariants remain a separate obligation.


## Pre-ray memory contracts for the complete aim query

`E1M1AimPreRayMemory.layout` is an address-only specification view: original
memory and ESP minus 28. `Later` describes protection during the ensuing path
query; `Read` additionally requires protection across the aim prologue and
setup. These are distinct because generated globals and callback arguments
cannot be required to preserve their old values across the stores that create
them. `safe`, `later` and `callback` derive the actual traversal guards from
these initial address conditions. `image` provides one protected-word image
for all catalog transports, including existing byte/halfword extraction proofs.

`PayloadSafe` covers line words, back-sector fields, object coordinates/radius,
object next links, the block-link global and selected block head. `payload`
transports their initial values and their later guards together. The complete
query no longer assumes any cell payload at a computed traversal-memory state.

`E1M1AimPreRayCatalog.Initial` holds actor/wall/portal data in initial memory,
with callback-stack views used only to express guards. Actor pointer/ID
correspondence remains an explicit representation condition. The shooter
pointer is supplied in initial EAX; `shooter` proves setup writes it to the
shooter global. No initial shooter-global contents or preservation premise is
required. `remaining` reuses the existing actor-entry, wall and portal image
lemmas, transports static callback/return guards, and constructs the complete
previous `Remaining` contract at the actual traversal boundary.

`E1M1AimPreRayQuery.execution` joins these transports with the preceding
continuous aim-entry theorem. Its premises contain no executed traversal-memory
catalog, payload or callback contract. The universally quantified `initial`
premise still indexes initial representation/arithmetic contracts by the actual
*pure source collection*, not an assumed machine endpoint. `decision` exposes
the same initial-only interface for the real center/right slope store and target
test. Bounds and decoded instruction maps are unchanged (fixed terms 264 for
return and 268 for decision). Returned values still correspond to the full
production `q.world.aimLineAttack` result.

This closes the outstanding **pre-ray transport of the query's machine-memory
contracts**. It does not prove those initial contracts hold on reachable E1M1
states, remove positive-range/source-success/arithmetic/capacity conditions,
execute all three autoaim queries, or rebase every restored caller register to
its pre-ray value. The selected-target image retains its existing collected
record/pointer relation.

Validation: `artifacts/e1m1-aim-pre-ray-query/validation.json`. Nine new named
proofs and their wrappers are included in the inherited strict axiom audit.
Seven new tests check protected-image requirements, the address-only callback
view, payload and guard transport, freshly written shooter identity, the lack
of computed traversal-memory premises, and original-return/source-result
connections. Eight preceding aim-entry tests are retained. All 262 prior
certificate-chain Doom sources and all 646 pre-turn Doom sources are unchanged.
No new byte ranges, runtime changes, decoder/instruction-semantic changes or
emulator rerun.

Next: expose the restored caller values and memory preservation needed by retry
setup, then instantiate this initial-only query interface for the three autoaim
probes. Reachable-state preservation remains a separate obligation.


## Original caller restoration and the next retry call

`E1M1AimCallerRegisters.saved` proves the four real prologue pushes save original
EBP/EDI/ESI/ECX in their corresponding slots. It uses the existing word-slot
separation theorem, including 32-bit stack wraparound. `SavedSafe` requires the
subsequent setup stores to avoid those freshly saved words; it does not require
them to preserve the memory that existed before the pushes. `setup_saved`
transports the saved values through setup. `restores` combines them with the
complete query's saved-word restoration and protected original return word.

The resulting `Restores` predicate refers to the pre-ray registers: ESP is
original ESP plus four, PC is the original return word, and EBP/EDI/ESI/ECX equal
their initial values. It asserts no EBX, EDX or flags preservation. The full
`E1M1AimRetryQuery.execution` theorem derives this predicate, retaining one
continuous aim-entry execution and the production source result. New saved-word
separation and original-return protection are explicit initial conditions.

`E1M1AimRetryRequest.execution` transfers the actual target test and retry
instructions into the same authenticated map. On a source target of `none`,
`ProbeResult` implies a null machine target, so the real decision reaches the
proper retry branch. It executes four decision instructions and five retry
instructions after the center probe, or four after the right probe. A numerical
zero slope by itself is not a miss premise.

`Request` gives the next call PC `0x2bb80`, the original query-entry ESP, actor
from original ESI, range `0x04000000`, and the proper angle derived from original
ECX. The center retry adds `0x04000000`; the right-to-left retry adds
`0xf8000000` to the already-rightward ECX. It also preserves ESI, tracks the new
ECX and proves the pushed return word (`0x2d7f8` or `0x2d819`). These are facts
about the actual reached next-query state, not an assumed callee result.

`E1M1AimRetryQuery.retry` derives these facts on a miss of the source result
already returned by the continuous execution. The extra controller premise
relates initial ESI to initial EAX and ECX to the current query angle. Thus the
next EAX equals the original shooter pointer and EDX has the correct offset
from that angle. The conclusion contains a conditional continuation from the
original aim entry, with exactly `n + 4 + (if second then 4 else 5)` instructions.
The maximum fixed bound term is 273 after a center miss or 272 after a right
miss. The query's returned state, source result and restored registers are still
available whether or not it misses.

`memory` and `frame` describe the **caller-side continuation only**: a slope
store at `0x2c0c0` and the new return-word push. Protected reads survive these
two writes. They do not imply preservation across the preceding entire aim
query. That larger memory frame, refreshed traversal stamps/capacity, and
next-angle geometry/table contracts still need to be connected before executing
the next complete probe. This is not yet the complete three-probe controller.
Reachable E1M1 justification remains separate.

Validation: `artifacts/e1m1-aim-retry-query/validation.json`. Nine new named
proofs and their wrappers are included in the strict transitive axiom audit.
Eight new tests check saved register provenance, setup/return protection,
original-stack restoration, miss/landing requirements, exact retry instruction
counts, request arguments/return words, two-write memory framing, initial-only
query premises and the conditional continuous retry. Seven preceding pre-ray
query tests are retained. All 265 prior certificate-chain Doom sources and all
649 pre-turn Doom sources remain unchanged. No runtime, decoder, instruction
semantics, binary-range changes or emulator rerun.

Next: carry the map/object/table memory and changed traversal bookkeeping across
the complete query, then use those facts to establish the next probe's input
contracts and execute it. The caller-register and retry-argument connections
are now available for that composition.


## Memory preservation through a complete aim call and retry

`E1M1AimCallerFrame.execution` extends the existing exhaustive mixed-hit loop
with `saved caller words ++ watched`. The existing loop supplies preservation
through continuing line/actor callbacks, target selection, exhaustion and early
stops. The original caller-restoration theorem consumes the saved-word portion;
the new result retains the additional watched words. The real return chain's
cursor write is then composed into the frame. Cursor separation is required
even on terminal queries that never enter a callback; callback protection is
only needed when the callback is entered.

`E1M1AimQueryFrame.execution` joins this frame to intercept collection and first
selection. Each watched word requires collection protection and callback
protection in the initial address-only stack view. Actual reached-state guards
are derived using the proved stack relation. The result preserves words from
query entry through the original caller return, alongside the same source
result, target image, slope and caller restoration.

`E1M1AimCallFrame.execution` moves the frame to actual aim entry `0x2bb80`.
Initial `Read` covers setup and collection; the callback guard uses initial
memory with the calculated future stack address. Payloads and catalogs are
transported by the preceding pre-ray theorems. The continuous execution combines
the 36 setup instructions with collection, ordered hits and return. It relates
to the full production `Scene.aimLineAttack`, restores original caller registers
and preserves every watched word. No reached memory equality is an assumption.
The instruction bound is unchanged.

`E1M1AimCallFrame.retry` extends that same execution on a source target of
`none`, using the preceding actual retry-call proof. Watched words must also
avoid the slope store at `0x2c0c0` and the original entry stack word, which the
retry overwrites with its new return address. Original-stack restoration
translates that initial separation into protection at the actual retry state.
The final frame reaches the next `P_AimLineAttack` entry, retaining the derived
shooter, angle, range, stack and return-word request. It covers both retry forms;
a zero returned slope alone is still insufficient to select a retry.

This proves a frame for any supplied finite list of suitably protected words.
It does not assert that memory is globally unchanged, that all next-query reads
have already been instantiated in that list, or that a next query has executed.
Traversal stamps/epoch and generated globals intentionally change, so the next
input contract needs their transition facts as well as this preservation.
Reachability, capacity and arithmetic success obligations remain separate.

Validation: `artifacts/e1m1-aim-call-frame/validation.json`. Four new named proofs
and authenticated-program wrappers enter the inherited strict axiom audit.
Contract tests reject missing setup/collection/callback/return protection,
claims about unwatched words, omitted retry-write separation, replacing a source
miss with a zero slope, and incorrect retry instruction counts. Earlier retry
regressions are retained. All 268 prior certificate-chain Doom sources and all
652 pre-turn Doom sources remain unchanged. No runtime, decoder, instruction
semantics, binary-range changes or emulator rerun.

Next: specialize preservation to the next probe's concrete read contracts and
connect changed traversal bookkeeping, then execute the next complete query.


## Next-probe input data and ray/setup

`E1M1AimRetryData` makes the preceding finite-word frame usable by input
contracts. `safe` transports aim/path setup protection using the restored ESP.
`mapReads` explicitly lists the five blockmap globals and every encoded
halfword address at stride two. `map` projects the preserved 32-bit loads to
16-bit blockmap words and reconstructs the complete map input including guards.
`cellReads` includes line geometry, the back-sector pointer, object x/y/radius,
next-object links, the global block-link pointer and the selected block head.
`payload` and `payload_safe` rebuild those values and reuse their setup guards.
Epoch, trace globals and line visit stamps are absent from this read set.

`E1M1AimRetryGeometry` defines the next angle with the real modular offset:
`0x04000000` after the center probe, or `0xf8000000` from the already-rightward
angle after the right probe. `angle_bits` relates the source angle to the retry
register expression. `samples` obtains the next angle's two entries from an
initial full trigonometric-table image, preserving only those selected reads
and the cosine pointer. `geometry` combines the samples with preserved shooter
fields and map origins; it transports all address-only layout guards using the
restored shooter pointer and stack. It does not assume a future ray result.

`E1M1AimRetryInputs.prepared` combines these facts into `Prepared`: next-angle
geometry at range 1024, the complete blockmap input, and payloads with guards for
a supplied finite list of cells. `Prepared` deliberately does not claim the
complete `E1M1AimSetupEntry.Inputs` contract. Its finite `reads` is the union of
map, geometry and cell read sets. The complete-call frame must protect that
specific set; it is no longer an arbitrary watched list whose application to
next-probe data is left to the caller.

`retry` applies the preceding continuous call theorem to these reads and derives
`Prepared` at the real next CALL on a source target of `none`. No next-state
payload, table image, geometry, memory equality or callee result is supplied as
an input. Initial full-table encoding and the supplied cells' initial payloads
remain explicit. The original call's source result, target image, registers and
frame are retained whether or not it misses.

`setup` runs the next actual ray/setup instructions in the existing authenticated
program. Its 36-instruction prefix is joined in `retry`, with derived
`OriginalPathInit.Inputs` and blockmap inputs at the next traversal CALL. The
combined count is `n + 4 + (if second then 4 else 5) + 36`. This executes the
next probe's setup, not its collection or ordered hit processing.

The next traversal still requires a new epoch/stamp-freshness argument, the new
trace, the actual next-angle route, capacity, callback/payload separation and
source hit catalogs. Supplied cells may cover that future route, but that
coverage has not been proved here. The existing stamp representation records
whether a word equals the current epoch; alone it does not constrain every
unvisited stamp relative to the following epoch, particularly at wraparound.
We must establish those conditions rather than assume freshness follows from
an increment. Reachable E1M1 and full three-probe correspondence remain open.

Validation: `artifacts/e1m1-aim-retry-inputs/validation.json`. Ten new named
proofs and their wrappers enter the inherited strict axiom audit. Tests cover
restored-stack guards, complete map encodings, halfword stride, actual object
link/back-pointer offsets, new-angle table and register obligations, shooter
identity, initial-only input reconstruction, the real retry request and the
continuous extra 36 setup instructions. Previous whole-call frame tests are
retained. All 271 prior certificate-chain Doom sources and all 655 pre-turn Doom
sources remain unchanged. No runtime, decoder, instruction semantics,
binary-range changes or emulator rerun.

Next: strengthen and carry the epoch/stamp transition to the retry boundary,
then assemble the next traversal-entry contract and connect its collection.


## Exact stamp history and next-epoch freshness

`E1M1AimStampImage.Image` strengthens the current-epoch/Boolean representation.
It retains the counter and an exact equation for each line: if its visited bit
is set, its word equals the epoch; otherwise it equals the corresponding word
in an origin memory. `start` constructs this image from the existing represented
history, including histories that already have set bits. `transport` moves it
across code that preserves the counter and stamp words.

`fresh` distinguishes the two ways a stamp can equal a later epoch. A visited
stamp needs the current epoch to differ from the future epoch; an untouched
stamp needs its original value to differ. `successor_ne` proves modular adjacent
epochs always differ, including `0xffffffff` to zero. `next_fresh` combines that
fact with an explicit original-word freshness condition. `bounded_fresh` gives
one sufficient initial condition: all old stamp values are numerically at most
the current epoch, and the next increment does not wrap. It does not assume this
condition is reachable or remove wraparound from the instruction semantics.

`restart` supplies the existing actual path-initialization theorem with the
derived freshness. Initialization increments the epoch and the resulting machine
memory represents the source's all-false visited array, under the existing
geometry and counter/stamp write-protection conditions. This is a reusable
component theorem; it is not yet connected to the complete retry witness.

`E1M1AimStampScan.step_image` reuses the existing exact `step_stamps` machine
summary. Duplicate lines leave their stamps unchanged and retain their already
set bit. New visits write the current epoch before geometric rejection,
acceptance or stopping. `scan_image` carries the strengthened image through an
early-stopping scan using its actual visited count; it never substitutes the
requested count for that count. `run_image` handles the continuing scan used by
aiming. `finished_image` includes the memory-preserving sentinel and real
iterator return. All four derive the image, rather than assume an output image.

`E1M1AimStampNextScan.execution` attaches the image to the existing real cell
line-scan execution and its ordered mixed collection. It lifts that unchanged
execution into the already authenticated complete-aim instruction map. The same
result has the original instruction bound, traversal-run relation, hit records,
Boolean history, protected-word frame and incoming-hit-prefix property, plus
the exact stamp image and conditional next-epoch freshness. `from_entry` chooses
the actual scan-entry memory as the origin and derives its starting image from
the preexisting representation, requiring no extra image premise.

The image still needs propagation through lookup, object scans, grid advance,
the whole mixed-cell route, ordered aim processing and return/retry. The generic
protected-word frame cannot substitute for this work during collection: visit
stamps are deliberately changed there. The full retry theorem therefore still
has an open next-epoch freshness connection. Reachable stamp bounds, future
freshness and other next-route/capacity/catalog conditions remain open; full
three-probe and whole-game correspondence are not claimed.

Validation: `artifacts/e1m1-aim-stamp-next-scan/validation.json`. Thirteen new
named proofs and their wrappers enter the strict inherited audit. Regressions
check actual stamp/counter preservation, both freshness conditions, the necessary
non-wrap bound, initialization protection, real mark values, early-stop prefix
length, continuing-scan premises and the authenticated sentinel instruction
count. A constructive memory example has a max-valued counter and an unvisited
zero stamp: the old representation holds, but freshness fails after wraparound.
Previous next-probe-input regressions are retained. All 274 prior
certificate-chain Doom sources and all 658 pre-turn Doom sources remain
unchanged. No runtime, decoder, instruction-semantic or binary-range changes;
no emulator rerun.

Next: propagate the exact stamp image through the remaining cell machinery and
route, then attach it to the complete query's return/retry state.


## Exact stamp history through complete cells and mixed itineraries

The previous line-scan image is now carried through the rest of collection:

- `E1M1AimStampCellTail.object_run` proves an exact word frame for actual object
  selection, linked-list scanning and return. Its `TailSafe` guard covers only
  those writes, so it applies to mutable line stamps without requiring a stamp
  to be separate from the preceding line scan's write to itself. `advance` joins
  the real numeric grid step and retains the same original-memory stamp image.
- `E1M1AimStampCell.scan` combines the line image with that object/grid result.
  `gate` derives the scan entry from the real map lookup; no later-cell stamp
  image is postulated. Existing source hit relations, capacity and data frames
  accompany the stronger image at the same reached machine state.
- `E1M1AimStampWalk` handles outside-map bounds returns, inside cells and finite
  mixed itineraries. Induction retains the same origin memory while accumulating
  the actual marked prefixes. Outside cells mark nothing, and repeated line IDs
  retain the accumulated visited history.
- `from_entry` lifts that itinerary execution to `E1M1AimProgramLink.program`,
  initializes its image from the entry invariant and derives next-epoch freshness
  from explicit entry-word freshness. The authenticated certificate reuses the
  same 51 DOS byte ranges and 828 map cells; there are no added binary ranges.

This is conditional on the existing itinerary, continuation, map/object memory,
stack separation and capacity contracts. It does not claim reachable-state
freshness, an automatically established next-probe route, or a complete second
or third probe. The collection relation is the existing mixed-cell relation;
the strengthened image still needs joining to the complete query initialization,
generated route, ordered hit processing, original return and retry. The prior
wraparound caveat remains: untouched old stamp values can equal a future epoch.

Validation: `artifacts/e1m1-aim-stamp-walk/validation.json`. Nine new theorems
are checked with the inherited certificate and strict axiom audit. Regression
contracts reject missing object-write guards, changed epochs, reset histories,
missing map/route/capacity premises and current-epoch freshness substituted for
future-epoch freshness. The previous 277 chain sources and all 661 pre-turn Doom
sources remain unchanged. No runtime/emulator checks were rerun.


## Exact stamp history through query collection, aiming and return

The stronger image now accompanies the continuous query execution, starting at
`P_PathTraverse` entry (`0x2c8a0`), through these connections:

- `E1M1AimStampLiveWalk` retains the image when matching the original line/object
  visit logs. It derives the cell itinerary and actual exit from the numeric grid
  state and counter, then joins the result to the finite loop used by the live
  source traversal. Source logs and stamps belong to the same reached state.
- `E1M1AimStampCollection.initialized_image` derives the new epoch and exact
  untouched stamp values from initialization. `collection` joins initialization
  to that generated loop and retains the original entry memory as the image's
  origin. The result reaches the actual ordered-hit setup boundary `0x2cafd`.
- `E1M1AimStampQuery` watches the epoch word and all 475 linedef stamp words,
  including unvisited ones. It carries the image through first selection, the
  derived callback invariant, all ordered-hit outcomes and the original return
  chain. The same authenticated execution retains `afterPath` correspondence,
  slope/target output, saved-caller restoration and the existing arbitrary
  watched-word frame. Next-epoch freshness is a consequence of explicit
  initial-word freshness, not a premise about the final memory.

Stamp protection is phase-specific: the collection phase permits line stamps to
be updated, while selection and ordered aiming require separation from their
own stack, hit-buffer and result stores. The existing generic whole-call frame
cannot be used unchanged for mutable stamps; the new proof composes the exact
collection image with the later frame instead.

This removes the supplied-itinerary premise from the strengthened theorem.
Static map/object encodings, metadata over the generated route, capacity,
initial freshness, arithmetic/catalog contracts and stamp-write separation are
still required. It is not a reachable-state theorem. The stronger image has not
yet been connected back through pre-ray aim setup or forward through the retry
CALL, and does not yet establish the next probe's full contracts. Whole aiming,
the complete three-probe controller and whole-game correspondence remain open.

Validation: `artifacts/e1m1-aim-stamp-query/validation.json`. Ten new theorems,
the inherited authenticated certificate, strict axiom audit and regression
contracts cover the numeric counter/route, exact origin memory, full stamp word
set, setup/ordered write guards and conditional future freshness. The same 51
DOS byte ranges and 828 map cells are used. All previous 280 chain sources and
664 pre-turn Doom sources are unchanged; no runtime or emulator checks rerun.


## Exact stamp history through aim entry, retry and next initialization

The strengthened stamp image is now connected across the next probe boundary:

- `E1M1AimStampOrigin` rebases an image across preserved stamp words and proves
  that accumulated mixed-cell history keeps its size. The existing setup-entry
  guards show that the preceding query image can use memory before the real aim
  prologue as its origin.
- `E1M1AimStampCall.execution` joins ray setup to the full query stamp proof,
  preserving the production `Scene.aimLineAttack` answer, original caller
  registers, target/slope result and arbitrary watched-word frame. `retry`
  derives the next CALL from `answer.target = none`, then preserves exact stamps
  across the caller's slope store and return-address push with explicit guards.
  A valid target with zero slope is not treated as a miss.
- `E1M1AimStampRestart.restart` takes the actual retry request and the next data
  derived by the existing read-frame proof. It reuses setup protection at the
  restored stack, transports the old image through the next 36 ray/setup
  instructions, and executes up to 175 path-initialization instructions under
  the same authenticated combined program. Successful next-axis divisions and
  original-word future freshness yield the next incremented epoch and an
  all-false 475-entry visited relation at the actual `0x2ca7f` loop gate.
- `E1M1AimStampRestart.retry` joins this to the complete original call: on a miss,
  the prefix runs from `0x2bb80` through return/retry, next ray construction and
  next initialization. Its next image starts at next-probe entry memory, retaining
  the actual old stamps rather than pretending that unvisited words reset.

No intermediate stamp image or freshness is assumed. Initial future freshness
remains an explicit conditional premise, including at modular wrap, and the
next source divisions must succeed. Static separation, source/catalog contracts
for the completed call and next-data read contracts remain necessary. This is
not yet a complete next cell-loop invariant or next probe: generated-route
metadata, capacity, callback encodings and ordered-hit catalog/arithmetic
obligations still need joining. Reachable-state freshness and the full
three-probe controller remain open.

Validation: `artifacts/e1m1-aim-stamp-restart/validation.json`. Seven new theorems
are checked with the inherited certificate and strict axiom audit. Regressions
cover origin preservation, source-target retry decisions, caller-write guards,
next-axis execution, incremented epoch, reset history and the next image's
correct origin. The chain still uses 51 authenticated DOS byte ranges and 828
map cells. All 283 prior chain sources and 667 pre-turn Doom sources remain
unchanged; no runtime or emulator checks rerun.


## Retry entry through the next generated collection

Three new modules connect the actual retry to the next collection exit:

- `E1M1AimNextContext` changes the context's epoch and ray, reuses the unchanged
  layout/payload guards, and reconstructs the next `AimSetupEntry.Inputs` and
  `QueryCollection.Entry`. Freshness follows from the preceding exact stamp
  image and an explicit initial future-epoch freshness premise.
- `E1M1AimNextCollection.execution` uses that entry to execute the next setup
  and complete generated cell route. Its numeric state, source collection,
  `pathTraverse` result, capacity bound, preserved words and exact stamp history
  agree at `0x2cafd`. The instruction bound is 211 plus the route bound.
- `E1M1AimRetryCollection.execution` joins the previous complete aim result,
  actual source-miss retry, preserved next data and this collection execution
  into one prefix starting at `0x2bb80`. The future route is generated from the
  next angle and its own metadata function, not the preceding route. Retry still
  requires target absence, not a zero slope.

No next request, prepared data, entry invariant, collection result or stamp
image is assumed at a reached intermediate state in the joined theorem.
Successful next-axis divisions, original future freshness, metadata and capacity
for the generated route remain explicit input contracts. Next ordered-hit
catalog/arithmetic contracts and ordered aiming remain to be connected. This
is not the full next probe, full three-probe controller or a reachable-state
correspondence theorem.

Validation: `artifacts/e1m1-aim-retry-collection/validation.json`. Six new
proof declarations, the inherited authenticated certificate and strict axiom
audit cover the next entry, actual collection and continuous retry execution.
Contract regressions reject the old trace, wrong stamp origin, omitted capacity,
wrong exit address and substitution of the preceding route. The chain still
uses 51 authenticated DOS byte ranges and 828 map cells. All 286 preceding chain
sources and 670 pre-turn Doom sources are unchanged. No runtime or emulator
checks were rerun.


## Two complete aim calls across the real retry

Three new modules connect the next ordered loop and return without assuming
its catalogs at a reached machine state:

- `E1M1AimRetryCatalog` defines the finite reads needed by the next collection's
  actor, wall and portal entries. It derives byte/halfword/word images from the
  shared word frame and transfers the pre-ray catalog, including pointer/actor
  identities and static callback guards. Stack restoration transports address
  protection. The actual request supplies the shooter register; old shooter,
  range, target and clipping-global values are deliberately absent from the
  read set because setup writes them.
- `E1M1AimNextCall.execution` reconstructs the next entry and catalogs from the
  prior memory, actual request, prepared data and exact stamp image. It reuses
  the existing complete call theorem for generated collection, ordered line and
  actor processing, clipping, stopping and return. The source aim result agrees
  with the returned target/slope. Watched words are related back to original
  memory, while the stamp image correctly starts at next-probe entry memory.
- `E1M1AimRetryPair.execution` strengthens the preceding call's watched set with
  the required catalog reads and joins both complete calls through the actual
  target-absence retry. The continuous prefix begins at `0x2bb80` and ends at
  `0x2d7f8` after the first retry or `0x2d819` after the second. Each call retains
  an explicit instruction bound, source path/aim results and caller restoration.
  A valid zero-slope target still does not trigger retry.

Initial next-probe catalogs are stated against original memory and the next
source collection, with explicit finite-read coverage. Source coverage and
arithmetic availability, map/object representations, successful divisions,
route capacity, future stamp freshness and memory/write separation remain
premises. The theorem does not prove them for reachable E1M1 states. Freshness
for a further call is still conditional on next-entry words. Joining the complete
three-probe decision/selection and establishing reachable-state invariants remain
open; this is not unconditional aiming or whole-game correspondence.

Validation: `artifacts/e1m1-aim-retry-pair/validation.json`. Ten new theorem
declarations are checked by the inherited authenticated certificate and strict
axiom audit. Regressions cover finite actor/wall/portal reads, original-memory
catalog transfer, restored-stack and shooter requirements, next-angle answers,
actual stamp origins, read coverage and exact controller return addresses.
The chain still uses 51 authenticated DOS byte ranges and 828 map cells. All
289 preceding chain sources and 673 pre-turn Doom sources remain unchanged.
No runtime or emulator checks were rerun.


## Live autoaim exits and the third request

The complete center/right pair is now connected to the controller outcomes:

- `E1M1AimControllerExit.accepted` executes the existing four-instruction target
  test/slope store followed by four pops and RET in the authenticated combined
  program. `center` and `right` connect these exits to the production
  `Scene.bulletAim` selection using the executed query answers. Target presence
  decides acceptance even when slope is zero. `last` separately authenticates
  the third probe's unconditional slope store and return; it does not establish
  a third source answer or the zero-on-miss property.
- `E1M1AimThirdRequest` composes the two exact marking histories. Two increments
  differ from the first epoch even across unsigned wrap; unvisited old words
  still require explicit original-memory freshness for that future epoch.
  The retry's slope and return-word stores preserve the derived freshness and
  exact image under the existing separation guards. Composed request equations
  give the third ray's original-angle offset `0xfc000000`, unchanged shooter,
  1024-unit range and `0x2d819` return word.
- `E1M1AimPairController.execution` joins these results to the actual center and
  right calls from `0x2bb80`. Either hit closes the production autoaim slope
  result and executes the original controller RET. Two misses instead reach
  the third call with the correct request, derived fresh stamps, the second
  probe's accumulated history and watched values preserved back to initial
  memory. Neither the third request nor its freshness/image is assumed at a
  reached state.

The joined theorem retains the existing source catalog/arithmetic contracts,
map/object representations, route metadata/capacity, division success and memory
separation premises. It adds original freshness for the third epoch, rather than
silently assuming no wrap or resetting old stamps. The third query body and
all-miss source closure still need joining, as does the controller prologue.
This is not a complete three-probe or reachable-state theorem.

Validation: `artifacts/e1m1-aim-pair-controller/validation.json`. Ten new theorem
declarations are checked with the inherited authenticated certificate and strict
axiom audit. Regressions cover source-based early exits, zero-slope target
semantics, modular angle/epoch wrap, original two-ahead freshness, retry write
guards, correct stamp origins and exact third-call arguments. The chain still
uses 51 authenticated DOS byte ranges and 828 map cells. All 292 preceding chain
sources and 676 pre-turn Doom sources are unchanged; no runtime or emulator
checks were rerun.


## All three autoaim queries through controller return

The third query body and the all-miss source case are now joined:

- `E1M1AimMissZero` proves an invariant of the actual source hit loop. Successful
  callbacks either continue, return a zero-slope miss, or return a present
  target. Induction carries this through the finite fold and through production
  `Scene.aimLineAttack`. An absent target therefore implies zero slope for any
  successful query. Failed divisions are excluded by successful execution,
  rather than an additional division-success premise in this invariant.
- `E1M1AimThirdCall` reconstructs the left ray's geometry, map/cell payload and
  actor/wall/portal catalog from original-memory reads preserved through the
  earlier calls. The full third query reuses the existing collection, ordered
  hit processing and return proof. It produces the actual source answer,
  target/slope relation, exact third stamp history and return to `0x2d819`.
- `E1M1AimThreeCalls.execution` joins the earlier pair, third request, third
  query and final store/pops/RET in one authenticated program. It returns a
  production `Scene.bulletAim` selection and matching stored slope for all four
  outcomes: center hit, right hit, left hit and three misses. The source invariant
  discharges the final controller's zero-on-miss premise. The theorem assumes
  no reached third state, probe answer or zero-on-miss property.

The continuous execution starts at the first `P_AimLineAttack` entry, not at the
`P_BulletSlope` prologue. Per-route original-memory representation/catalog,
source arithmetic, capacity, future freshness and separation conditions remain
explicit. The theorem's final observation is the production selection and DOS
slope store, not a complete post-return global-state relation. The next connection
is the actual controller prologue plus its caller-state/target frame; reachable
E1M1 preservation is a separate remaining obligation. This is not unconditional
whole-aiming or whole-game correspondence.

Validation: `artifacts/e1m1-aim-three-calls/validation.json`. Eleven new theorem
declarations are checked by the inherited authenticated certificate and strict
axiom audit. Regressions require actual successful source queries, absence,
loop preservation, original reads, the third counter/freshness, read coverage,
capacity, exact return PC and the joined source/stored-slope result. The chain
still uses 51 authenticated DOS byte ranges and 828 map cells. All 295 preceding
chain sources and 679 pre-turn Doom sources are unchanged; no runtime or emulator
checks were rerun.


## Autoaim controller entry and caller restoration

The three-query suffix is now connected to the actual outer entry and caller:

- `E1M1AimControllerEntry` lifts the original nine-instruction prologue and CALL
  into the same authenticated program as the aiming queries. It derives the
  first request's shooter, facing, 1024-unit range, saved controller registers,
  stack and `0x2d7d5` return word from original memory and the four-push angle-read
  separation guard. The exact five-store memory image and saved outer register
  words are proved, including stack wraparound. Its general frame theorem can
  transport original words that are separate from those five writes.
- `E1M1AimControllerFrame` proves the four pops and RET restore the caller's
  register words and outer return address. It accounts for the final slope
  store's separation from those words and the retries' EBP/EDI preservation.
  Rebasing the result through the actual prologue recovers the original caller
  values, not assumed values supplied after any query.
- `E1M1AimControllerCall.suffix` strengthens the previous three-query execution
  with this frame on every outcome. Five stack words are included in the
  existing watched set and therefore survive the actual queries and retries.
  `execution` prepends the prologue and derives the previously supplied first
  controller-register and resume-PC premises. The continuous prefix starts at
  `0x2d7c0`, stores the production autoaim slope, and returns to the original
  outer return word with ESP advanced by four and EBX/ECX/EDX/ESI/EBP/EDI restored.

The query data contracts still refer to the first-call state deterministically
constructed from controller entry. They are explicit input predicates, not
assumed query outcomes. Their wholesale transport to pre-prologue memory and
preservation for reachable E1M1 states remain to be proved. The final theorem
also does not yet export exact selected-target encoding or a complete global
memory frame. Those gaps are distinct from the now-joined entry/return control
flow. Unconditional aiming and whole-game correspondence remain open.

Validation: `artifacts/e1m1-aim-controller-call/validation.json`. Twelve new
theorems are checked with the inherited authenticated certificate and strict
axiom audit. Regressions cover the exact prologue PC/count, original angle and
stack guards, saved-register order, protected slot coverage, slope-store
separation, outer return PC, restored registers and wrapping stack arithmetic.
The chain still uses 51 authenticated DOS byte ranges and 828 map cells. All
298 preceding chain sources and 682 pre-turn Doom sources remain unchanged;
no runtime or emulator checks were rerun.


## Returned target observation and original-memory inputs

The controller call now retains the target image alongside its slope and caller:

- `E1M1AimWindowTarget` proves that every successful production aim query has
  `answer.target = answer.window.map Window.target`. Successful callbacks
  preserve that identity, induction carries it through the actual finite hit
  fold, and the source extraction connects it to `Scene.aimLineAttack`. No
  additional source-window agreement assumption is introduced.
- `E1M1AimControllerTarget` proves the existing target pointer and conditional
  aim-slope image survive accepted and final returns. `Observed` relates that
  image to the production selection window. The final left-hit/all-miss
  correspondence now exports it, with no assertion about the stale aim-slope
  global on a miss.
- `E1M1AimControllerData` transports the original full trig-table image and
  arbitrary future stamp freshness through the five prologue writes under
  explicit separation guards. Current-counter transport is also proved.
- `E1M1AimSelectedCall` joins those facts to all branches of the continuous
  entry-to-caller execution. Its outer theorem takes tables and both future
  freshness predicates from pre-prologue memory; the earlier deterministic
  first-call versions are derived. Source selection, bullet-slope store, caller
  return/stack/register restoration and the final target observation all refer
  to the same executed final state.

The exported pointer relation deliberately retains the older collected-record
witness: matching record ID and exact `resolve(record)` value. That older image
does not include the selected record's actor-kind tag. Strengthening the witness
and deriving direct `objects(window.target)` equality remain distinct work;
there is no implicit equation between a Lean ID and a DOS address. Other query
input contracts still refer to the deterministic first-call state. Reachable
E1M1 invariants, complete original-memory transport and a global memory frame
remain open; this is not unconditional aiming or whole-game correspondence.

Validation: `artifacts/e1m1-aim-selected-call/validation.json`. Eighteen new
theorems are checked by the inherited authenticated certificate and strict
axiom audit. Regressions require successful source queries, both preserved
target globals, original table contents, stack-write protection, original
freshness, the earlier source misses, and the final target/caller guarantees.
The chain still uses 51 authenticated DOS byte ranges and 828 map cells. All
301 preceding chain sources and 685 pre-turn Doom sources are unchanged;
no runtime or emulator checks were rerun.


## Actor provenance and direct target pointers

The target image now retains enough information to identify the DOS actor:

- `E1M1AimActorHit` strengthens exhaustive callback execution with the selected
  record's `isLine = false` tag. It derives the tag from the executed actor
  branch and the original/work-record relation. Line stops remain null-target;
  skip/continue cases preserve the old traversal and memory contracts.
- `E1M1AimActorOrdered` carries that stronger exit through the terminating
  nearest-first loop, preserving watched caller words and stack shape. The
  existing arithmetic availability, history, budget, catalog and separation
  premises are unchanged.
- `E1M1AimActorCaller` and `E1M1AimActorQuery` retain the tag through nested
  returns and continuous collection-to-query-return execution. `object_pointer`
  derives `targetGlobal = objects id` from the actor-tagged witness. There is
  no assumption that wall IDs and actor IDs differ, or that an ID is a pointer.
- `E1M1AimActorObservation` preserves the stronger image across actual accepted
  and final return states, and translates successful source query windows to
  direct pointer observations. The left-hit/all-miss adapter retains the
  original null-target and stale aim-slope behavior.
- `E1M1AimActorDecision.execution` appends the actual four-instruction
  center/right target test and bullet-slope store to the continuous query.
  The same execution exports the stronger image, direct object-pointer and
  conditional aim-slope equalities, matching bullet slope, and hit/retry PC.
  It starts at `0x2c8a0`; the initial saved return word supplies the controller
  address. No final target, reached query answer, or endpoint PC is assumed.

The strengthened result is joined through one query and its real decision.
The full prologue/three-probe aggregate still uses the prior weaker image;
substituting this stronger query result through its entry/retry wrappers is
next. The existing map/object/catalog, arithmetic, capacity, freshness and
separation predicates still require reachable-state justification. A complete
global memory frame and unconditional aiming correspondence remain open.

Validation: `artifacts/e1m1-aim-actor-decision/validation.json`. Seventeen new
theorems are checked by the inherited authenticated certificate and strict
axiom audit. Regressions reject using the older untagged image for a direct
object-pointer claim, reject all-wall buffers for a selected actor, require
real loop budgets and arithmetic, and check actual source/return/decision
contracts. Null-target observations intentionally impose no aim-slope equality.
The chain still uses 51 authenticated DOS byte ranges and 828 map cells. All
305 preceding chain sources and 689 pre-turn Doom sources are unchanged;
no runtime or emulator checks were rerun.


## Direct actor pointers through the complete controller

The stronger target image is now joined from original controller entry to
caller return, with no new input assumptions:

- `E1M1AimActorCallerFrame` retains the actor-tagged image together with
  protected caller words. `E1M1AimActorStampQuery` combines it with the exact
  line-stamp history of the same collection and aiming execution.
- `E1M1AimActorStampCall` prepends ray setup and carries the result through the
  actual miss-triggered retry. `E1M1AimActorNextCall` and
  `E1M1AimActorRetryPair` reconstruct the next query using the preserved reads
  and fresh epoch, retaining the stronger target image for both answers.
- `E1M1AimActorPairController` handles center/right acceptance and the second
  retry. `E1M1AimActorThirdCall` executes the left query from the original-memory
  data and derived third-call request. The existing stamp transport, freshness,
  catalog reconstruction and instruction proofs are reused.
- `E1M1AimActorController.suffix` joins all four outcomes: center hit, right hit,
  left hit and all miss. `execution` prepends the original prologue and exports
  the production selection, matching stored bullet slope, outer return PC,
  caller ESP and six saved registers, and the direct actor-pointer observation
  after the final return. A hit gives `targetGlobal = objects(window.target)`
  and the matching aim-slope global. A miss gives a null pointer without
  incorrectly requiring the old aim-slope global to have been cleared.

All ten strengthened theorem signatures have exactly the same input binders
as their predecessors; the contract regression checks that explicitly. The
result starts at `0x2d7c0`, rather than assuming a post-query answer or return
state. No source-target or pointer-equality premise is introduced. This closes
the earlier gap between the local strong-image adapters and the full controller
aggregate. The older weak-image aggregate and all earlier Doom sources remain
unchanged.

This remains conditional correspondence. Most map/object and catalog contracts
still describe the deterministic first-call state, while trig tables and future
freshness are already supplied from pre-prologue memory. Transporting the
remaining contracts and proving them for reachable E1M1 states are the next
obligations. Arithmetic success, intercept capacity, pointer/memory separation,
stamp freshness and the wider global memory frame are not silently discharged.
This does not prove unconditional aiming, rendering, audio or whole-game parity.

Validation: `artifacts/e1m1-aim-actor-controller/validation.json`. Ten new
proof declarations are checked with the inherited authenticated certificate
and strict axiom audit. Regressions cover unchanged input binders, protected
caller/stamp words, real query entry, miss-only retries, future epochs,
retained read images, both target witnesses, direct object mapping and the
final caller return. The chain still uses 51 authenticated DOS byte ranges
and 828 map cells. All 311 preceding chain sources and 695 pre-turn Doom
sources are unchanged; no runtime or emulator checks were rerun.


## Original-memory inputs for complete aiming

The input side of the full controller theorem now refers to original memory:

- `E1M1AimControllerInputs.layout` is a pure specification view: first-call
  registers and stack addresses, with unchanged entry memory. `registers`
  proves the actual prologue realizes that register layout using the original
  angle value and its existing save-write protection.
- `SafeReads` requires separation of finite input reads from the five actual
  prologue writes. `kept` derives their word image from execution; `map`,
  `payload` and `catalog` reuse the established retry transport proofs to
  rebuild blockmap inputs, cell encodings/object links, and actor/opening
  catalogs from the original values. No original shooter-global value is
  required where setup creates it.
- `E1M1AimControllerSetup.setup` transports the complete first-query setup,
  including geometry, blockmap, current epoch word and freshness of each
  current stamp. Its finite read set covers the current counter and stamps,
  so their relationship survives the same writes, including wrapping arithmetic.
- `E1M1AimOriginalInputs.execution` supplies those derived contracts to the
  complete three-probe theorem. Initial, right and left query payloads/catalogs
  now come from original memory with explicit prologue protection. Address-only
  guards are transported through the proved register equality. Trig tables and
  both future freshness predicates retain their existing original-memory form.

The final theorem conclusion is identical to `E1M1AimActorController.execution`:
continuous original controller entry through caller return, matching source
selection and stored bullet slope, direct actor pointer, conditional aim slope,
outer return PC, stack and saved registers. There are no input references to the
executed first-call state. The pure layout does not execute a memory write or
serve as an assumed reached state. Unlike the prior target-image strengthening,
this transport adds explicit read/write separation premises, which remain to
be justified along with the original representation and arithmetic predicates.

Next: discharge static representation/layout guards for the admitted E1M1
setup, then prove preservation of the dynamic actor, opening, stamp, capacity
and arithmetic conditions through supported play. A wider global memory frame
is still needed for composing aiming into complete game execution. This is
conditional aiming correspondence, not an unconditional all-inputs or
whole-game theorem.

Validation: `artifacts/e1m1-aim-original-inputs/validation.json`. Seven new
theorems are checked by the inherited authenticated certificate and strict axiom
audit. Regressions cover the unchanged-memory layout, wrapping stack arithmetic,
rejection of actual stack-write aliases, required original values and finite
read guards, absence of reached-state input predicates, and the unchanged final
pointer/slope/caller guarantees. The chain still uses 51 authenticated DOS byte
ranges and 828 map cells. All 319 preceding chain sources and 703 pre-turn Doom
sources are unchanged; no runtime or emulator checks were rerun.


## Range guards for aiming entry

The next reduction of original-memory aiming assumptions is implemented by
`E1M1AimRegions`, `E1M1AimStaticRegions`, and `E1M1AimAllocatedEntry`.

- Reuse the existing byte-region separation theorem. Twenty bytes of stack
  reserve contain all five real controller stores. A covered read set is safe
  from those stores even when its fields are unaligned or span several regions.
- Prove coverage using fixed DOS offsets and E1M1 dimensions: 3461 blockmap
  halfwords, 475 linedefs at stride 62, the shooter prefix through offset 68,
  setup globals and the complete 10240-entry sine/cosine table. Sample coverage
  reuses `thrust_table_index` and holds for every 32-bit angle. The generated
  certificate instantiates map coverage with the pinned extracted WAD words.
- Connect those facts to the real controller-entry transport. `inputs` produces
  the actual first-query setup contract, preserved table image and register
  equality; `fresh` preserves the original stamp freshness for any supplied
  epoch. `setup_safe` directly provides the prologue setup guard used by the
  complete controller theorem. Generic region coverage remains available for
  later actor/cell catalog work.

The exact protection envelopes are explicit. Blockmap words occupy 6922 bytes,
while four-byte preservation windows require 6924 bytes. The extra two bytes are
part of the guard envelope, not an assertion about the loader's allocation.
The globals envelope asserts separation only from the stack, not immutability.
The twenty-byte reserve covers only this prologue, not the complete query's
stack usage. Nonwrapping intervals are sufficient conditions; the older
byte-level theorems remain unchanged for wrapping addresses.

This closes the finite address calculations **given region placement**. It does
not establish that initial or reachable DOS states satisfy that placement, nor
does it derive original map/object encodings, inner-query guards, fresh epochs,
capacity, or successful divisions. The next useful connection is to the actual
startup memory representation and allocation facts, with dynamic actor/cell
regions handled separately. The complete outer controller result is inherited
unchanged; no broader claim of whole-game equivalence follows from this step.

Validation: `artifacts/e1m1-aim-allocated-entry/validation.json`; inherited pinned
51 DOS ranges and 828 map cells, strict axiom audit, region-boundary and contract
mutation tests, and full proof build. All 706 pre-turn Doom sources remain
unchanged. Runtime behavior and instruction semantics are untouched.


## Map protection through query setup

This advances the memory/stack package of the reachable-aiming checklist beyond
the outer prologue. Three new modules reuse the existing byte-region theorem
and the unchanged query execution/transport proofs:

- `E1M1AimSetupFootprint` reduces every field of `E1M1PathMapQuery.Safe` to a
  finite footprint: 13 fixed globals plus a conservative stack window through
  offset -104 from query entry. This includes the existing axis/intercept helper
  and iterator-entry protections. The actual later helper slot at -104 is
  explicitly tested. From outer controller entry, the sufficient reserve is
  124 bytes because its prologue consumes twenty bytes.
- `E1M1AimMapRegions` proves the five blockmap globals are byte-disjoint from
  those fixed stores, and derives every blockmap word's protection from region
  placement. The fixed-store envelope is `[0x13580,0x2c1ec)`; its use for heap
  separation does not imply that all globals within it are written or immutable.
  In particular the traversal counter is deliberately not treated as preserved.
- `E1M1AimMapEntry.Values` contains only width, height, table/list/line pointers
  and the original halfword image. `inputs` constructs all remaining map guards
  for the fixed 36-by-23 map and 3461 words. `execution` supplies the unchanged
  original query prefix through its real path-traversal CALL and the map contract
  at that boundary. `controller_map` derives the same query-entry contract after
  the real outer prologue, from pre-prologue memory; it needs no angle-content
  premise because map data are independent of the angle registers.

The 6924-byte map protection envelope still extends two bytes past the 6922-byte
halfword payload, as required by the existing four-byte preservation windows.
The generated certificate instantiates the new map constructor using the
inherited pinned WAD array and its kernel-checked word count.

This is a conditional layout-to-guard result, not an initial-state proof. It
removes individual blockmap setup protection premises but retains actual data
encodings and region placement. Dynamic actor/cell and opening catalogs,
callback and ordered-loop protection, capacity/arithmetic/freshness obligations,
and reachable-state establishment/preservation remain. The 104/124-byte bounds
must not be presented as complete aiming stack bounds. The full outer aiming
controller theorem is inherited unchanged; no runtime or decoder is modified.

Validation: `artifacts/e1m1-aim-map-entry/validation.json`; strict inherited axiom
audit, fixed-store and stack-boundary regressions, contract mutation checks and
full proof build. All 709 pre-turn Doom sources are unchanged. The same 51 DOS
ranges and 828 map cells remain pinned; no emulator rerun or new binary ranges.


## Actor and opening region protection

This continues the memory/stack work toward reachable-state aiming. The new
proofs cover exactly the actor/wall/portal fields in `E1M1AimRetryCatalog.reads`.
`E1M1AimObjectRegions.Storage` supplies a nonwrapping prefix bound and separation
from the stack and fixed-global write envelope. Read-only objects need not be
pairwise disjoint. The prefixes are 108 actor bytes, 62 linedef bytes and 8 sector
bytes, including unaligned front/back pointers at offsets 46 and 50. The actor
flags byte at offset 104 uses the existing four-byte transport window, requiring
protection through offset 107 rather than merely offset 104.

`E1M1AimCatalogRegions.Layout` provides these regions for each actual hit and
represented portal. `located` proves coverage of the complete read set, including
empty catalogs and aliases between front and back sectors. `read` derives the
query-setup portion of each old read guard; later collection and first-selection
frames are still explicitly required. `prologue_safe` derives all catalog read
protection against the earlier outer-controller writes.

`E1M1AimCatalogEntry.OtherInputs` retains exactly the old pre-ray catalog fields
except `actorReads`, `wallReads` and `portalReads`. Its object representation,
pointer identity, ordered-callback stability, saved-word and global protections
are not weakened. `initial` rebuilds those three read families from layout plus
later frames; `remaining` feeds the result into the existing real query setup
transport. `controller` constructs the catalog after the actual outer prologue
from original-memory contracts and the existing original-angle guard. It does
not assume a reached memory or register image. The shooter needs its separate
angle guard because it need not be present in the hit catalog.

Separately, `opening_safe` accounts for the original opening helper's own four
stack saves and four fixed-global writes. The same line/sector regions and a
sixteen-byte helper stack reserve discharge its prior pairwise protection
premise. `opening_heights` applies the unchanged original-helper theorem to
obtain signed ceiling minimum and floor maximum. It retains the original memory
image, sector pointers and non-sentinel side condition; it does not establish the
call site's full invariant or replace the authenticated execution chain.

Remaining: DOS startup/allocation and live object representation, cell payload
coverage, collection/ordered-hit memory frames, saved/caller/global protection,
capacity/arithmetic/freshness, and invariant preservation over reachable play.
This is progress on setup/prologue guards and one deeper helper, not completion
of all callback protection or unconditional aiming correspondence.

Validation: `artifacts/e1m1-aim-catalog-entry/validation.json`; strict inherited
axiom audit, shared-sector/unaligned-field/boundary checks, contract mutations,
exact retention of the other catalog fields, and full proof build. All 712
pre-turn Doom sources remain unchanged. The same 51 DOS ranges and 828 map cells
are pinned; no runtime/decoder changes or emulator rerun.


## Collection and ordered-read region protection

This extends the previous catalog setup protection through collection and the
first selected callback, and derives the persistent word guard used by the
ordered callback/mark/scan memory frame.

`E1M1AimWalkRegions` derives the non-stamp fields of
`E1M1FiringMapState.Safe`, all of `E1M1AimEntryFrame.SafeWord`, and
`E1M1AimMapFrame.StableWord` from the existing object-region separation and a
conservative reserve of 212 bytes below the `q.sp` context anchor. This accounts
for line scan helpers, object callbacks/fraction helpers, iterator entry,
first-selection stores and callback return/local slots. The actual deepest
object-fraction guard is at `q.sp-212`. The fixed-global envelope already
contains the complete 128-record intercept buffer, its cursor, opening outputs
and clipping globals. Its use here discharges address-separation requirements;
it does not prove the buffer has sufficient capacity on every reachable query.

Visit stamps require a field-level argument. `E1M1AimStampRegions.line_field`
proves byte-disjointness between any four-byte read ending before offset 54 and
every stamp at offset 54 in the 475-record, 62-byte-stride linedef array. The
proof cancels the common base and works even when that base wraps. It includes
the unaligned pointer read at offset 50, whose final byte is 53; offset 51 is
rejected because it overlaps the stamp. Thus no impossible separation between a
line and its own array is required. Actor and sector reads use explicit external
prefix separation from the nonwrapping linedef array. The new layout records
bounded line identities and these representation conditions. `stamps` derives
the complete catalog-read stamp guard from them.

`E1M1AimCollectionEntry.later` combines those results. The strengthened `initial`,
`remaining` and `controller` constructors reuse the previous joins but no longer
accept their separate collection/first-selection read premise. `stable` derives
the persistent ordered-read guard, and `word` applies it to the existing complete
callback/mark/minimum-scan frame. The latter still requires that frame, the
selected record pointer and a bounded record index; it does not infer execution
from memory separation alone.

The unchanged `OtherInputs` fields, real memory contents/object correspondence,
initial/live allocation, cell payload protection, remaining record/callback/
caller/global invariants, arithmetic success, capacity, stamp freshness and
reachable-state induction remain obligations. The 212-byte reserve is relative
to `q.sp`, not an automatically established live stack bound. Address separation
of stamps must not be confused with freshness of their values or handling of
counter wraparound. The complete aiming theorem remains conditional.

Validation: `artifacts/e1m1-aim-collection-entry/validation.json`; inherited
51 DOS ranges and 828 map cells, strict axiom audit, same/adjacent-linedef and
wrapping-base tests, overlap/deepest-slot/buffer checks, contract mutations and
full proof build. All 715 pre-turn Doom sources are unchanged; no runtime or
instruction-semantic changes, new binary ranges, or emulator rerun.


## Cell payload protection through original setup

`E1M1AimCellRegions.index_bound` derives the row-major index bound from the
original signed cell guard for the pinned 36-by-23 grid. `head_address` relates
the original bitvector shift to the four-byte table stride; `head_located`
then protects every selected head within 3312 bytes, including the last word
at index 827. The address identity permits wrapping arithmetic, but the storage
criterion deliberately requires a nonwrapping region. This does not infer
actual heap allocation from an address calculation.

The cell layout uses one region for all 475 linedefs and bounded line IDs;
each line's relevant fields end before byte 54. Vertex coordinates need eight
bytes, actor x/y/radius/list-link reads need the first 68 bytes, and read-only
prefixes may alias. Each region avoids the stack and the existing global-write
envelope. The fixed input word at `0x2c0f8` is inside that envelope, so it is
handled separately: an exact finite byte proof shows that it avoids every
actual setup-global store. Only its stack separation remains a placement fact.

`reads` and `covered` derive the full existing `cellReads` set. In
`E1M1AimCellEntry`, `reads_safe` and `safe` discharge all six fields of the
existing `PayloadSafe` contract. `traversal` plugs them into the unchanged
setup-to-traversal memory transport. `controller` additionally follows the
actual outer prologue: its five stack writes preserve the original payload,
the original shooter-angle value/guard supplies the real register layout, and
the payload then survives query setup. The 124-byte reserve below the outer
entry ESP supplies the existing 20-byte prologue and 104-byte setup guard.
This is a sufficient bound for these named guards, not a whole-query bound.

The endpoint is the reached traversal boundary with the existing payload and
setup protection reconstructed there. Collection-time cell frames are a
separate next connection: in particular vertices and actor prefixes must avoid
linedef visit stamps. Initial/live allocations, memory encodings, other
caller/callback/record invariants, capacity, successful arithmetic, freshness
and induction over reachable play remain unproved here. No execution, decoder,
runtime or binary-range semantics were changed.

Validation: `artifacts/e1m1-aim-cell-entry/validation.json`; 13 new kernel-checked
theorems, inherited 51 pinned DOS ranges and 828 cells, strict axiom audit,
signed-grid/last-head/wrapping-address/prefix-boundary tests, retained-premise
mutation checks, previous regression suite and full proof build. All 718
pre-turn Doom sources are unchanged; emulator evidence is inherited, not rerun.


## Cell payload protection during collection

The previous entry/setup guard is now extended to the collection phase.
`E1M1AimCellStamps.Layout` retains the prior storage contract and requires vertex
prefixes, actor prefixes and the blocklinks table to avoid the linedef array.
The existing line-field byte theorem handles reads inside that same array:
those fields end before the visit stamp at offset 54. All 475 possible stamp
writes are covered, not just the lines in the currently selected cell. Fixed
globals use the line array's existing separation from the global-write envelope.
These remain placement hypotheses, not a proof of DOS's allocator or all live
object placement.

Collection has a smaller write footprint than setup. `E1M1AimCellWalk.word`
derives the existing complete collection read guard from stack separation,
intercept-array/cursor protection and stamp separation. `buffer_word` bounds
all three words of every one of the 128 intercept records within the exact
buffer envelope. `global_array` proves that the initialized trace words, active
flag and blocklinks pointer avoid that buffer and its cursor. Combined with
the existing 212-byte reserve below `q.sp`, this protects those globals during
collection even though setup writes some of them. Buffer address coverage still
does not imply that a query cannot overflow the buffer.

`reads_safe`, `scene_safe` and `selection_safe` discharge the existing cell
payload, complete scene-image and selected-blockhead protection fields. The
scene includes the initialized trace/active globals absent from the initial
payload. `E1M1AimCellCollection.images` then transports every future cell image
using region placement, initial images and an existing collection frame; it no
longer needs an entire `Static` contract merely to obtain its protection fields.
`lookup_ready` connects the derived scene guard to the actual DOS line lookup
and freshly written callback word, retaining numeric/layout contracts, actual
scan pointers and stack-position facts. `setup_then_collection` composes the
previous setup theorem with payload transport across an existing collection
frame, without an independently assumed intermediate payload.

Remaining obligations include original/live allocation and encoding, other
caller/callback/record guards, numeric/division contracts, buffer capacity,
visit freshness and reachable-state induction. These joins still require the
execution frames and scan facts named in their statements; address separation
does not establish execution or the full reachable aiming contract by itself.
No runtime, decoder, machine semantics or binary range changed.

Validation: `artifacts/e1m1-aim-cell-collection/validation.json`; 14 new theorems,
strict inherited axiom audit, adversarial vertex/actor/head stamp aliases,
exact buffer endpoints, setup-versus-collection global checks, retained-premise
mutations, prior suite and full proof build. All 720 pre-turn Doom sources are
unchanged. Same 51 DOS ranges and 828 pinned cells; no emulator rerun.


## Derived traversal and callback handoff guards

`E1M1AimCallbackRegions.Layout` states separation between the stack and both
the bounded linedef array and existing fixed-global envelope. Alongside the
212-byte reserve below `q.sp`, this supplies complete-word containment for the
relevant stack offsets and separation from all 475 visit stamps, the 128 hit
records, and the cursor. This is a sufficient representation contract; actual
DOS stack and heap placement still needs establishment for admitted play.

A byte-level `above` theorem separates reads at offsets 4 through 64 from
collection writes at offsets 68 through 212. The relative proof works for any
stack base, including wrapping translation. Allocation-based uses still require
the nonwrapping reserve. `upper_collection` uses this result to reconstruct the
existing collection guard for those upper words. The endpoint is byte-precise:
a read at offset 65 overlaps the write at offset 68 and is not admitted.

`selection` derives all six traversal-prologue store guards for every hit record
and the cursor, as well as their protection against the final callback CALL at
`q.sp-140`. `initial` protects the saved callback pointer at `q.sp-44` through
path initialization and axis setup, using the actual entry relation
`ESP=q.sp-52`. `callback` combines this with collection protection. The pre-ray
join derives this path-entry relation from the existing aim-entry relation
`ESP=q.sp-24` and the explicit 28-byte setup layout; no reached register image
is introduced as a new premise.

`E1M1AimCallbackEntry.execution` and `decision` retain the exact existing complete
query and subsequent center/right-decision conclusions. Their three separate
handoff premises (`separated`, `callbackSafe`, `cursorCall`) are replaced by the
region/reserve inputs and constructed internally. All other premises are kept:
entry geometry and memory, Common/Static collection contracts, scene/payload
facts, capacity, source correspondence and catalog conditions. The decision
also retains return-word protection and the original return-address value.
The new joins therefore do not establish reachable-state preservation, capacity,
freshness, all remaining memory guards, or unconditional aiming correspondence.

Validation: `artifacts/e1m1-aim-callback-entry/validation.json`; 12 new theorems,
strict inherited axiom audit, upper-word adjacency/overlap and wrapping-translation
checks, concrete callback protection, erroneous stack-position rejection,
record/cursor aliases, missing-premise mutations, previous suite and full proof
build. All 723 pre-turn Doom sources remain unchanged. Same 51 pinned DOS ranges
and 828 map cells; no runtime, decoder or instruction-semantic changes, and no
emulator rerun.


## Derived saved caller and callback return protection

This extends the existing stack/line/global placement contract to saved-state
protection during ordered hit processing. `E1M1AimSavedRegions.above` proves
byte separation between caller words at offsets 4 through 136 below `q.sp` and
ordered-processing writes at offsets 140 through 212. The relative argument
works for any stack base; allocation-based applications still require the
nonwrapping reserve. Offset 137 overlaps the callback return word at offset 140
and is excluded. `ordered` combines this separation with the existing buffer,
cursor and global region proofs. `protect` adds the target and slope stores
performed when an actor is selected.

`saved` specializes to all eight words in the existing saved-caller list:
offsets 120, 116, 52, 40, 36, 32, 28 and 24 below `q.sp`. This includes the
traversal's saved register, nested return addresses, and the outer aiming saves
and return word. `actor_return` separately protects the seven callback return
words at offsets 140 through 164 against actor-selection target/slope stores.
These latter words are freshly written by the callback prologue; they are not
claimed unchanged through that prologue.

`restores` reuses the actual completed return-chain theorem with the derived
saved-word guards. Its preserved image and final stack-position premises remain:
separation is not substituted for proof of execution or correct saved contents.
`E1M1AimSavedEntry.OtherInputs` retains exactly the predecessor catalog fields
except `saveSafe` and `savedSafe`. `other` reconstructs those two fields, and
`initial`, `remaining` and `controller` pass the result into the existing catalog
joins. The separate catalog-read placement and caller-stack placement contracts
are both retained. No reached memory image is introduced as an input.

Remaining obligations include `callerReads` through setup/collection, other
catalog/helper/record guards, actual initial/live allocation and encoding,
numeric/source correspondence, capacity, visit freshness, and reachable-state
induction. The 212-byte reserve remains a sufficient bound for named memory
guards, not a universal stack bound. Complete aiming correspondence remains
conditional; the runtime and executable semantics are unchanged.

Validation: `artifacts/e1m1-aim-saved-entry/validation.json`; 10 new theorems,
strict inherited axiom audit, upper-word adjacency/overlap and wrapping-base
checks, positive saved-word protection, actor-store alias rejection, unchanged
residual-field audit, missing-premise mutations, previous suite and full proof
build. All 725 pre-turn Doom sources remain unchanged. Same 51 pinned DOS ranges
and 828 cells; no runtime/decoder/instruction-semantic changes or emulator rerun.


## Derived caller reads through path setup and collection

`E1M1AimCallerRegions.above` separates caller words at offsets 4 through 52
below `q.sp` from path-setup writes at offsets 56 through 212. Its byte argument
is translation-independent, including wrapping bases; placement-based uses
still require the nonwrapping reserve. The boundary is exact: offset 53 can
overlap the first save at offset 56. `setup` derives path initialization and
axis-setup protection using the real path-entry relation `ESP=q.sp-52`.
`selection` covers the six intercept prologue stores, cursor update and callback
CALL; collection protection reuses the previous upper-stack theorem.

`path_guard` combines those three components. `later` transfers this address
contract to the explicit path-entry layout used at aim entry, requiring
`ESP=q.sp-24`. `callers` specializes it to the six existing offsets 84, 96,
100, 104, 108 and 112 relative to the ordered-loop base `q.sp-136`: actual
addresses `q.sp-52`, `q.sp-40`, `q.sp-36`, `q.sp-32`, `q.sp-28`, `q.sp-24`.
`word` applies the derived guards to the existing setup/collection/selection
memory frame. This retains execution as a premise rather than inferring a
memory equality solely from address separation.

The phase distinction matters for the first word: the CALL into path traversal
creates its return address at `q.sp-52`. It must survive subsequent path setup
and collection, but it must not be assumed unchanged from the earlier aim-entry
memory. The new theorem derives `Later`, not the stronger pre-ray `Read`, for
these words. A regression check explicitly rejects the stronger whole-setup
preservation claim for the newly written path return address.

`E1M1AimCallerEntry.OtherInputs` removes only `callerReads` from the predecessor
contract. `other` reconstructs it; `initial` and `remaining` reuse the existing
catalog joins with the actual aim-entry stack relation explicit. `controller`
derives that relation from outer `ESP=q.sp-4` through the existing 20-byte
prologue layout. Original angle values/guards, catalog contents and all other
fields remain unchanged. Initial/live placement and memory values, remaining
fixed-global/helper/record guards, arithmetic/source contracts, capacity,
freshness and reachable-state induction remain obligations.

Validation: `artifacts/e1m1-aim-caller-entry/validation.json`; 11 new theorems,
strict inherited axiom audit, adjacency/overlap and wrapping checks, concrete
path-entry protection, newly created return-word rejection at the earlier
phase, outer/query stack relation checks, unchanged residual-field audit,
missing-premise mutations, prior suite and full proof build. All 727 pre-turn
Doom sources remain unchanged. Same 51 pinned DOS ranges and 828 cells; no
runtime/decoder/instruction-semantic changes or emulator rerun.


## Derived fixed-global protection by aiming phase

`E1M1AimGlobalRegions` names the six globals created by aim setup: range, eye
height, shooter, lower slope, upper slope and target. Their addresses are
contained in the fixed-global envelope and separated from every intercept
record field and the cursor. `collection` derives their complete collection
write guard, including line visit stamps. The new `Layout.linesGlobals`
premise separates the linedef allocation from fixed globals; the previous
line/stack and global/stack separation alone cannot justify this. A regression
example satisfies the old stack layout while placing line zero's stamp exactly
over the shooter word, and is rejected by the new layout.

`path_setup`, `selection` and `later` combine individual fixed-store separation
with the existing 212-byte stack reserve. They protect values after aim setup;
they do not falsely preserve the old globals through the setup that creates
them. `ordered` protects only range, eye height, shooter and target through
continuing callbacks. The lower and upper slopes are intentionally excluded:
clipping writes them. Target selection may write target and final slope, so
this theorem does not substitute for the stronger selected-actor frame.

`clip` protects ceiling, eye height and upper slope across floor clipping.
`floor_word` applies this derived guard to `E1M1AimFloor.result`, using the
existing actual helper frame theorem at `ESP=q.sp-164`. The callback starts at
`q.sp-140`; accounting for that 24-byte difference is part of the proof.

`E1M1AimGlobalEntry.other` reconstructs seven predecessor fields: `query`,
`clip`, `valueReads`, `shooterSafe`, `shooterLater`, `targetSafe`, `globalReads`.
`initial`, `remaining` and `controller` connect them to the existing catalog
joins, retaining the actual entry stack relation, original angle value/guard,
and separate catalog placement premises. The residual `OtherInputs` has five
fields: `layout`, `portals`, `shooterReg`, `actors`, `walls`. This count is not a
completion percentage: `layout` bundles multiple helper/record contracts, and
the catalogs still require memory contents and pointer/identity correspondence.

Next is deriving the remaining callback/helper and record-layout guards from
region placement, then connecting initial/live memory representations. Actual
reachable allocation, sufficient intercept capacity, fresh stamps, numeric and
source contracts, and preservation under gameplay remain obligations. The new
line/global separation is a sufficient representation contract; its truth for
reachable DOS states is not established here. No runtime behavior changes.

Validation: `artifacts/e1m1-aim-global-entry/validation.json`; 14 new theorems,
strict inherited axiom audit, clipping/target/setup phase counterexamples,
line/global alias rejection, final intercept slot coverage, retained-premise
mutations, prior suite and full proof build. All 729 pre-turn Doom sources
remain unchanged. Same 51 pinned DOS ranges and 828 cells; no runtime, decoder
or instruction-semantic changes and no emulator rerun.


## Derived complete fixed callback layout

`E1M1AimHelperRegions.opening_reads` derives read protection across the callback
prologue and opening helper from stack/global placement and fixed-store
separation. `read_word` extends that result to the clipping stores. `record_word`
specializes it to the interval from the start of the hit buffer through the end
of the cursor word, ending exactly at the first opening-global address.
Containment includes all four bytes: the cursor at `0x2c028` fits, but a word
starting one byte later overlaps the opening globals and does not fit.

`records` covers all three fields of every hit given `hits.size≤128`; `cursor`
covers the cursor read. These are callback read guards, not `StableWord` claims
covering the parent's cursor update or selected-fraction mark. Tests reject
those stronger guards. An oversized array with a record at index 129 would
alias an opening-global store, demonstrating why arbitrary unbounded arrays
cannot be covered. The chosen 128-record bound is a sufficient interface
condition, not a new proof that every admitted E1M1 query obeys it.

`clipping_reads` protects eye height and the initial lower/upper slopes through
opening, before clipping writes the bounds. `return_safe` derives protection
of the seven callback return/save words from opening and clipping globals.
`helper` protects the opening helper's return word and saved registers. All
use the actual callback stack relation `ESP=q.sp-140`, the inherited region
placement, and the sufficient 212-byte reserve anchored at `q.sp`.

`layout` assembles all eleven fields of `E1M1AimCycleInvariant.Layout`, reusing
the earlier selection handoff and upper-stack protection theorems for the
remaining stores and callback slot. `callback_records` then applies the derived
record guard to the actual `E1M1AimWindow.result`. Its mapped-line inputs and
pre-callback `Encodes` memory image remain explicit; address separation alone
does not establish correct data or execution preconditions.

`E1M1AimHelperEntry` removes only `layout` from the previous residual inputs.
The initial, traversal and outer-controller joins derive it and retain capacity,
placement, stack relations, original angle and all four remaining fields:
`portals`, `shooterReg`, `actors`, `walls`. The three object catalogs include
object-specific memory protection as well as contents and identity. Those
nested guards are the next target; four fields must not be read as four small
remaining tasks or a progress percentage.

Actual reachable allocation/encoding, numeric and source contracts, intercept
capacity, fresh traversal stamps and preservation under gameplay remain open.
The full aiming and whole-game correspondence claims remain conditional.

Validation: `artifacts/e1m1-aim-helper-entry/validation.json`; 14 new theorems,
strict inherited axiom audit, satisfiable concrete full layout including empty
and full-capacity arrays, exact byte-boundary and last-record checks, oversized
array/global alias rejection, parent-store phase checks, missing-premise
mutations, prior suite and full proof build. All 731 pre-turn Doom sources
remain unchanged. Same 51 pinned DOS ranges and 828 cells; no runtime, decoder
or instruction-semantic changes and no emulator rerun.


## Derived actor wall and portal catalog protection

`E1M1AimObjectCatalog` separates memory contents from persistent address guards.
`ActorValues` retains the flags byte, z and height equalities. `PortalValues`
retains the line-hit classification, full opening image (including side and
front/back pointers), and two-sided flag. `WallValues` retains line-hit
classification and the non-two-sided flag. None contains `StableWord`, `Apart`,
or a storage/layout assumption.

`actor`, `portal` and `wall` use the existing storage-prefix field lemmas and
`E1M1AimWalkRegions.ordered` to construct the original entries. The actor prefix
is 108 bytes because the existing guard protects a full four-byte word at the
flags offset 104, although the value is read as a byte. The line prefix is 62
bytes and each sector prefix is eight bytes. Read-only objects need not be
separated from each other: front and back may be the same sector. Unaligned
line pointer fields at offsets 46 and 50 remain covered.

`actors`, `portals` and `walls` lift those constructors to the original hit
collection using the existing `E1M1AimCatalogRegions.Layout`. Actor versus line
classification selects the correct storage prefix. Array bounds and the
bidirectional pointer/shooter identity relation are preserved. The constructors
do not invent flag, pointer, height or z values from separation.

`actor_preserved` applies the derived actor entry to the existing actual cycle
frame theorem. It retains the execution frame, equal reached stack pointer,
selected-record address and bounded index. This connects the new constructor
to successive-hit preservation without assuming a future actor image.

`E1M1AimObjectEntry.OtherInputs` retains four named fields, but replaces the
three guarded catalogs with contents/classification/identity contracts. Its
`other` theorem reconstructs the predecessor inputs. The initial, traversal
and controller joins use `placement.objects` already supplied by the stamp
layout; no new object-separation premise is introduced. Actual input memory
supplies all values. The callback specification view changes only ESP and does
not represent an executed memory transition.

The next task is to derive these contents and identities from initial/live
map and actor representations. Region placement and stack reserve remain
explicit assumptions, as do reachable intercept capacity, stamp freshness,
numeric/source correspondence and gameplay preservation. This completes the
address-guard derivation for these residual catalogs, not every hypothesis of
the complete aiming theorem and not the reachable-state proof.

Validation: `artifacts/e1m1-aim-object-entry/validation.json`; 11 new theorems,
strict inherited axiom audit, concrete actor entry with actual zero memory,
wrong shootability rejection despite safe storage, shared-sector and unaligned
field checks, exact 108-byte prefix/wrap boundary checks, fixed-global alias
rejection, identity/content/frame premise mutations, residual contract audit,
prior suite and full proof build. All 733 pre-turn Doom sources remain unchanged.
Same 51 pinned DOS ranges and 828 cells; no runtime, decoder or instruction
semantics changes and no emulator rerun.


## Portal contents from original loader execution

`E1M1AimLoadedPortal.pointers` reuses `E1M1LineLoad.establishes` and the exact
original result to obtain both cached sector pointers from the raw side-index
and side-table contract. `back_index` follows the second halfword copy through
both pointer stores. It respects the original ordering: the second source read
happens after the first destination write, with the existing `nextRead`
separation retained. The copied index is not supplied as an output premise.

`flags` proves the copy/cache/advance suffix preserves the line flags byte,
including wrapping line addresses. `sectors` preserves the four sector height
words under explicit separation from both halfword copies and pointer stores.
Read-only front/back sector aliasing is allowed. `image` combines these results
with a present back-side index into the existing aiming opening image. `values`
adds the original line classification and two-sided flag. `wall` handles the
solid-wall flags without requiring any back-sector image or side-presence fact.
These proofs do not establish the initial flag or sector height values.

`transport` carries portal values through equality of exactly eight read words:
flags, side index, two cached pointers and four heights. It derives byte and
halfword transport from those word equalities. `catalog` applies the previous
storage-based catalog constructor to a later aiming state using that frame.
The frame across intervening execution remains explicit: this is not a claim
that arbitrary startup/gameplay leaves sector heights unchanged. Sector updates
need a correspondence/preservation argument for updated values.

`execution` pairs the derived portal values with the existing uninterrupted
original loader run from `0x2e358` to the next-record/cleanup boundary. This is
one loader suffix, not the full initialization sequence. No fictitious actor
initialization relation was introduced to broaden the milestone.

Validation now combines the inherited 51-range aiming certificate with the
three existing `original-line-load`/`original-line-cache` ranges: copy, cache,
and advance. Extraction rechecks the pinned executable and relocations, and
kernel proofs identify each extracted byte list with the existing decoder.
The existing strict loader axiom audit is chained with the aiming audit.
Changes to any of the three extracted byte lists are rejected by tests. This
adds no decoder, semantics or new machine-code model; emulator diagnostics
were not rerun.

Validation: `artifacts/e1m1-aim-loaded-portal/validation.json`; 10 new theorems,
constructive raw-side-table example whose cached fields initially are zero,
non-sentinel versus absent-side checks, shared-sector and overwrite rejection,
wrapping flags preservation, retained source/value/frame/storage contracts,
prior regression suite and full proof build. All 735 pre-turn Doom sources
remain unchanged; 54 pinned ranges and the same 828 blockmap cells.

Next: carry loader-established fields through the remaining startup phases,
and derive actor contents/identity from their actual representation. Initial
allocation, sector updates, numeric/source contracts, intercept capacity,
fresh stamps and reachable-state induction remain separate obligations.


## Portal preservation through the complete line scan

`E1M1AimLoadedScanRegions` derives byte separation for the original loader's
word, halfword and sixteen-byte stack write footprint. Nonwrapping array bounds
and an earlier/later record ordering establish record disjointness, without
assuming alignment. Sector prefixes must be disjoint from line and stack
writes; they may alias each other. These are sufficient storage conditions,
not evidence that DOS startup has already allocated those regions correctly.

`portal_reads` covers the flags word, back-side index word, cached front/back
pointers and four sector-height words. `sector_safe` discharges the earlier
single-suffix sector protection contract from the same bounds. The ranges
cover both straight-axis bodies and the diagonal FixedDiv call's stack writes.

`E1M1AimLoadedScan.iteration_suffix` identifies the existing full iteration's
result with the loader suffix started from that iteration's actual `copyInput`.
`established` constructs its portal values, then `retained` applies the existing
whole-loop suffix frame theorem to all later records. This handles an empty
suffix for the last record as well. No memory equality across later iterations
is assumed, and no matching final portal image is supplied by the caller.

`execution` pairs the established portal with the uninterrupted original loop
from `0x2e29a` to `0x2e3c1`. It retains the existing loop layout, initial count
and cursors, and per-iteration arithmetic safety contract. The latter is not
silently discharged by the separate pinned WAD delta certificate: connecting
those deltas to actual loaded memory remains an obligation.

The source/flags/height premises are at the reached suffix, not yet derived
from all initial loader inputs. The new result stops at line-loop cleanup;
transport through later startup and subsequent sector changes remains open.
This is a concrete reduction of the portal initialization/frame obligation,
not unconditional aiming or whole-game correspondence.

Validation: `artifacts/e1m1-aim-loaded-scan/validation.json`. Twelve new proof
declarations are checked with strict inherited and full original scan audits.
The certificate joins six existing metadata/slope/geometry byte ranges with
the inherited 54 distinct ranges, deduplicating and checking the shared range
metadata. Executable and WAD identities must agree. All six newly joined byte
ranges have negative mutation tests. Tests also cover adjacent unaligned line
records, first/last record bounds, shared sectors, partial overlap, insufficient
stack space, array wraparound and retained source/arithmetic/value premises.
The prior suite and full proof build pass, with all 736 old Doom sources frozen.
No runtime, decoder or instruction semantics change; no emulator rerun.

Next: derive the reached suffix's source/flags/sector premises from the initial
loader representation, reusing existing source-image preservation proofs, then
connect the completed line image through the remaining startup work. Actual
allocation, live sector updates, actor identity, capacity/freshness and
reachable-state induction remain separate obligations.


## Initial loader images to the portal scan

The reuse check found the exact earlier results needed: `E1M1LineOutput` already
preserves its initial side image through the loader and constructs the reached
copy-source contract; `E1M1LineSource` already derives arithmetic safety from an
initial geometry image. Neither result is reproved or changed in this batch.

`E1M1AimInitialPortal.source_at_copy` connects `image_preserved`, the reached
register invariant, and `copy_source`. Its existential source also records that
the back-side index is the initial record's index, preserving the sentinel
case. The portal's pointer identity comes directly from that initial record.

`sector_word_at_copy` joins the existing loop suffix frame, region-based sector
write protection and current-prefix `copy_frame`. `sectors_at_copy` assembles
the four resulting equalities. Thus the final `established` theorem needs only
initial sector values, not values postulated after earlier loader work. Sector
updates during later gameplay are outside this interval.

`execution_from_image` reuses `scan_from_image` (and its underlying
`arithmetic_of_image`/`safe_of_source` chain). It pairs the final portal with
the exact complete original loop output, requiring the initial geometry image,
static separation and finite `good` geometry facts rather than successful
arithmetic in every reached state. This does not prove initial WAD-to-memory
representation or actual heap/stack allocation.

The reached two-sided flag remains deliberately visible in both final theorem
signatures. It is not inferred merely from a non-sentinel back side. Next is
the raw metadata-to-reached-flag connection, using the existing ordered metadata
copy theorem and preserving its output through the geometry prefix. Then the
remaining startup phases can consume the completed line image. Reachability,
actor representation, changing sectors, capacity and stamps remain open.

Validation: `artifacts/e1m1-aim-initial-portal/validation.json`. Five new theorems
and six explicitly reused declarations are strictly audited with the inherited
60-range certificate. A constructive synthetic one-record example starts with
zero cached pointers, copied index and flags, and establishes actual original
loop execution plus a complete portal from raw side/vertex/sector data. This
example proves its concrete reached flag by kernel reduction; the general flag
obligation remains. Negative checks retain source images, separation, initial
sector values, side presence, classification, reached flag, initial loop state
and finite arithmetic safety. The prior suite and full proof build pass; all
738 old Doom sources are frozen. No runtime/decoder/semantics changes, new byte
ranges, or emulator rerun.


## Raw metadata flags to the portal image

`OriginalLineSetup.metadata_fields` already proves that the raw flag halfword
is copied. The missing boundary was preservation *after* that copy: the existing
whole-iteration frame excludes the metadata destination, so it cannot prove the
flag it intentionally writes. `E1M1AimLoaderFlags` adds this narrower frame,
reusing vertex/delta, FixedDiv and bounds memory results. It follows the actual
axis/diagonal branch definitions and covers CALL, saves and return stack writes.
It does not change or reprove the metadata copy's instruction execution.

`flag_byte` combines that frame with the existing halfword copy result to prove
exact equality with the raw low byte. It preserves every flag bit, including a
clear two-sided bit, and accepts wrapping line addresses under explicit stack
separation. No alignment or back-side-presence inference is introduced.

`E1M1AimRawPortal.flag_stack` derives the current record's stack guards from the
already-used array layout and stack reserve. `flag_at_copy` uses the earlier
loop frame to preserve the selected raw flag before its iteration, then applies
the new copy result. Protection of that raw read against earlier records is an
explicit static address condition; it is not an assumed reached memory image.

`established` and `execution_from_image` use that equality to replace the final
reached flag premise. Their content assumptions now refer only to initial side,
vertex, sector and raw flag data. The general execution theorem has no supplied
reached content image or per-reached-state arithmetic assertion. Initial images,
finite good-geometry facts, separation and initial loop representation still
must be established from DOS startup. This is initialization support for the
conditional aiming theorem, not a proof of arbitrary reachable aiming states.

Validation: `artifacts/e1m1-aim-raw-portal/validation.json`. Eight new theorems,
strict inherited and new axiom audits, and the unchanged 60-range byte chain.
Constructive horizontal, vertical and diagonal one-record examples establish
complete original loop execution and portal output from initial raw contents.
The reached flag is obtained through the general proof in these examples.
Checks retain static raw-read/stack protection, initial flag and independent
back-side presence; a clear flag stays clear. The local flag theorem is also
instantiated with a wrapping line address. The previous suite and full proof
build pass; all 739 preexisting Doom sources remain frozen. No runtime, decoder,
instruction semantics or authenticated byte ranges changed; no emulator rerun.

Next: connect the initial loader images to the pinned map's DOS memory
representation and carry the completed image through the remaining startup
phases, reusing the existing source-image/grouping proofs. Actor initialization,
actual storage placement, live sector updates and reachability remain separate.


## Authenticated map encoding to portal execution

`E1M1AimEncodedPortal.Row` holds logical geometry, full 16-bit flags, side and
sector indices, and initial fixed-point sector heights. A separate address
function relocates sector identities. `Encoded` specifies only consumed bytes
of raw linedefs, decoded vertex words, side-pointer words, global bases and
portal sector heights. The raw record's unrelated fields and all other memory
remain unspecified. This is a representation contract, not a synthetic
initializer masquerading as original DOS execution.

The six new theorems decode those bytes using `E1M1NoiseImage.read_half` and
`read_word`, construct the existing geometry/side images, extract the flag's
low byte, establish the sector values and apply `E1M1AimRawPortal`'s complete
line-loop execution join. Front/back sectors may share addresses when their
byte values agree. Absent back sides produce a zero target without demanding
back-pointer bytes or back-sector heights. Front presence remains a generic
premise, discharged for the pinned map by the certificate.

The verifier rechecks the shareware WAD hash and reuses the validated E1M1
lump structure, geometry and topology. It extracts full flags and signed sector
heights, converts heights to 16.16 words, and checks raw index/flag provenance
against the existing geometry/topology records. The generated 475-row literal
is an artifact, not a runtime data dependency. Nine kernel-checked declarations
establish row count, loader arithmetic safety, front/back presence conditions,
agreement with the previous delta list, their per-index forms, and the complete
original 475-record execution paired with a selected portal output.

The pinned execution theorem removes separate finite `good`, `fronts` and
`present` premises. The selected map row must still be two-sided; its initial
byte representation, storage bounds/separation and loop-entry representation
remain premises. Python parsing and SHA256 bind literals to WAD bytes; there is
no newly verified WAD parser. Most importantly, no theorem yet says actual DOS
startup establishes `Encoded`. This batch makes that remaining boundary exact.

Validation: `artifacts/e1m1-aim-encoded-portal/validation.json`; six new generic
proofs and nine pinned checks/joins with strict inherited axiom auditing. Tests
include a constructive encoded-memory-to-original-execution example, missing
back-side behavior, low-byte little-endian flags, rejected wrong byte contents,
required sector images, changed WAD/provenance rejection and a geometry mutation
rejected by the existing delta link. The prior suite and full proof build pass;
all 741 old Doom sources are frozen. There are no new instruction ranges,
runtime/decoder/semantics changes or emulator reruns.

Next: connect the actual startup loaders to the byte representation, beginning
with the existing side-pointer loader results, and preserve it to line-loop
entry. Actor startup, actual allocation, later startup stages and reachable
state preservation remain separate.


### Original side writes to aiming encoding

`E1M1AimSideEncoding` joins the existing `OriginalSideLoader` results to
`E1M1AimEncodedPortal`. It proves the converse of the existing byte-reader
relation for a 32-bit word, including arbitrary unaligned and wrapping
addresses. It then derives the side-table-global bytes after the authenticated
publication segment and each side-pointer word after the authenticated
11-instruction linking suffix. The sector address is the relocated sector-array
base plus 86 times the nonnegative sector index. The actual scratch store and
subsequent sector-base read remain those of the existing machine semantics.

`row_encoding` combines front and optional back emissions with preservation of
only their consumed bytes into a common memory. It also retains the original
suffix execution equalities. A missing back side needs no back suffix entry;
shared side addresses need no artificial front/back disjointness. `row_source`
constructs the existing raw-line side source, and `initial_encoding` constructs
`Encoded` without assuming its side-pointer image. The other initial byte
images remain explicit premises. `link_retains` derives preservation across a
later suffix from its real two-write footprint, including its stack temporary.

The certificate extends the inherited aiming/line-loop chain with the two
already modeled original side-loader ranges. It authenticates their bytes
against the same executable, rewrites the new execution wrappers to the
extracted bytes, and strictly audits both chains. Four finite-data declarations
check the pinned rows' front and present-back sector-index bounds and use them
to construct suffix input contracts. The existing WAD-to-literal parser/hash
trust boundary is unchanged.

Validation: `artifacts/e1m1-aim-side-encoding/validation.json`; 18 tests across
the new and prior suites, 731 proof-build jobs, 2,712 audited declarations and
62 distinct original instruction ranges. The constructive fixture starts with
zero cached side pointers, executes a front suffix, preserves it through a back
suffix, and feeds those results into the complete one-record linedef loader and
portal theorem. Separate checks cover absent/shared sides, wrapping addresses,
a scratch write actually destroying an earlier pointer, rejected omitted frame
and index/separation premises, and rejected executable-byte mutation. All 742
pre-turn Doom sources are frozen. No runtime, decoder or instruction semantics
changed; no emulator cross-check was rerun.

Boundary: `Kept` is a preservation contract, not evidence of intervening startup
execution. The local input contracts do not establish the enclosing side-loader
loop, allocation, or WAD loading. The new constructor advances the initial-data
part of reachable aiming; it is not a proof of full startup or reachable-state
parity. Next: connect these local suffix contracts through the enclosing
side-loader control flow and its intervening writes/calls, preserving emitted
pointers to line-loop entry. Reuse existing allocation/loader frame results
where available rather than re-proving the aiming algorithm.


### Side-loader loop advance and pointer preservation

`OriginalSideAdvance` adds authenticated ranges `[0x2e4d1,0x2e4dd)` (the signed
loop latch) and `[0x2e46a,0x2e47e)` (the next record's offset stores). The
existing pointer-emission path transfers into the joined program without a
state reset. A 15-instruction execution reaches the next side at `0x2e46a` or
cleanup at `0x2e4dd`; a continuing 22-instruction execution reaches the first
texture-lookup CALL at `0x2e47e`. These counts include the 11-instruction suffix
already proved in `OriginalSideLoader`.

The abstract endpoint retains instruction ordering: the loop count is loaded
after the suffix's scratch/pointer writes; the next record's second signed
16-bit offset is read after its first 32-bit offset store. The new proofs do
not assume those reads see the initial memory. `E1M1AimSideAdvance` derives
all relevant register strides (30 bytes on disk, 18 in memory), counter
increment, stack preservation, and the correct signed test. A count below
2^31, an in-range counter, and separation of the count from both prior writes
supply ordinary finite-loop reasoning. Zero/negative/wrapping inputs remain
covered by the unconditional instruction-level theorem.

The pointer just written occupies bytes +14 through +17 of the old record;
next-record offsets occupy +18 through +25. The existing modular slot-separation
proof discharges their disjointness, including address wraparound. Thus the
new continuing theorem carries the pointer's byte image through the next
record's offset prefix without an assumed frame. The last-record theorem
instead carries the image to cleanup. These are concrete reductions of the
previous `Kept` obligations for this interval, not a claim about texture calls
or arbitrary later startup writes.

Validation: `artifacts/e1m1-aim-side-advance/validation.json`; 17 new proof
declarations in two new modules, 18 tests across the new/prior suites, 733
proof-build jobs, 2,751 audited declarations and 64 authenticated original
ranges. Tests cover both complete intervals, signed-overflow/zero-count gates,
a scratch write that changes the branch by clobbering the count, aliased offset
reads, wrapping pointer preservation, rejection of missing count/branch
premises, corrupted opcode bytes, and invalid extraction metadata. All 743
pre-turn Doom sources are unchanged.

The independent Unicorn run checks 240 local executions against a separate
word/memory calculation, including count/sector-global aliases, counter signed
edges, negative sector indices and next-offset source/destination aliases.
It compares every modeled general-purpose register, the exact endpoint,
instruction count, ordered writes and all mapped data bytes. It does not claim
full hardware-flag equality or full startup execution. The first sandboxed run
failed in Unicorn host CPU initialization before emulated code; the authorized
outside-sandbox rerun passed. No old decoder, instruction semantics or runtime
was changed.

Next: cover the texture-lookup CALL/return boundaries and their field stores,
then carry the established side-pointer image to the next suffix entry. The
loader's allocation, initial entry, cleanup, and later startup stages remain
separate obligations. This is still initial aiming data (checklist item 1),
not a replacement of the completed conditional aiming algorithm.


### Texture caller continuations and the next pointer write

`OriginalSideTextures` authenticates `[0x2e47e,0x2e4af)`: three CALLs to
`0x34750`, the actual continuations at `0x2e483`, `0x2e494`, `0x2e4a5`, and the
caller stores ending at the sector-pointer suffix. Each return first writes
full EAX to the stack scratch word, reloads it, then stores low AX at side-record
offset 8, 10 or 12. Before subsequent CALLs the next name argument comes from EDI
or ESI. The proofs retain exact stack pushes, return addresses, flags and write
ordering, including aliases between scratch, texture fields and return slots.

`E1M1AimSideTextures.caller_path` composes these 14 caller instructions with
three actual helper execution prefixes in an enclosing program. Each helper
prefix must begin at the exact state created by the preceding CALL and end at
its exact continuation PC. The theorem does not assume an abstract texture
oracle, invent a RET, or claim the helper paths exist. `linked_path` then joins
the established caller endpoint with the existing 15-instruction pointer suffix
and signed latch, carrying the emitted side-pointer byte representation. Its
bound is 29 plus the actual helper instruction counts. Post-texture pointer
inputs remain explicit until their raw/global/register preservation is derived.

The caller frame separates its real scratch stores, 16-bit field stores and
return-address pushes. Composing it with three helper word-frame facts preserves
an incoming pointer image to the next suffix entry. The previous side's pointer
(+14) is provably separate from this side's texture fields (+18+8, +18+10,
+18+12), with modular byte addresses and no nonwrapping-heap assumption. Remaining
stack separation is explicit; an alias fixture demonstrates that a CALL push
can overwrite a just-written texture field, so no unjustified field-retention
claim is made.

Validation: `artifacts/e1m1-aim-side-textures/validation.json`; 18 new theorems,
18 tests across the new/prior suites, 735 proof-build jobs, 2,792 audited
declarations and 65 distinct authenticated original ranges. Tests verify exact
return addresses, low-halfword truncation, the full-word scratch value, wrapping
field separation, rejected missing helper paths/frames and post-texture inputs,
wrong return PCs, corrupted call/field bytes and invalid extraction metadata.
A test-only RET fixture instantiates the general composition theorem and checks
the three field values and a preserved pointer; it is explicitly not a DOS
lookup implementation or lookup certificate. All 745 pre-turn Doom sources
remain unchanged.

An independent Unicorn cross-check executes 384 original caller-segment cases,
stopping at helper entry or at the sector-pointer suffix. It compares all eight
general-purpose registers, flags, exact PCs, instruction counts, ordered writes
and all mapped data memory, including overlapping scratch/field/return slots.
It does not execute or replace the lookup body. Unicorn's write hook sometimes
reports full EAX for a 16-bit write, so the harness masks hook values to the
reported write width and independently compares the actual resulting memory.
The corrected harness and full certificate pass. No runtime, old decoder or
instruction semantics changed.

Next: discharge the helper execution/register/frame contracts with the original
texture-lookup body, starting with its wrapper and successful return path. Its
inner name search, absent-texture behavior and missing-name error branch must
remain explicit until proved or excluded by the pinned startup data. Then use
those contracts to preserve suffix inputs and the side-pointer image across
complete iterations. Loader entry/allocation/cleanup and later startup remain
separate obligations.


## Original texture lookup wrapper

The next initialization link now covers `R_TextureNumForName` at original
code offset `0x34750`. The certificate authenticates the 35-byte wrapper and its
original data relocation. The instruction proofs cover the four-instruction
entry through the call to `0x346f0`, the three-instruction result gate, and the
four-instruction success epilogue. The error body is authenticated as bytes but
its execution is not claimed: a missing result reaches `0x34760`.

The entry saves EBX and EDX, passes the name in EAX/EDX, and pushes `0x34759`.
Saved-slot proofs also preserve the wrapper caller's return word, for arbitrary
32-bit stack addresses including wraparound. The return restores EDX/EBX,
returns the search result in EAX, and advances its incoming ESP by 12.

The composition theorem uses an actual inner-search `Prefix`, not a texture
oracle or synthetic RET. Successful wrapper execution takes at most the inner
prefix length plus 11 instructions; the missing-result path takes at most the
inner length plus 7 to the error boundary. A continuation theorem exposes the
exact return PC required by the preceding three-call side-loader composition.
The inner search must still preserve the saved words and any protected pointer
word. These are explicit obligations, and its register/stack state is not
inferred from the helper's name.

Validation: 15 new public theorems; 7 new and 9 preceding-suite tests; 737 proof
build jobs; 2,825 strictly audited declarations; 66 authenticated code ranges;
128 independent Unicorn cases covering aligned/unaligned stacks, all three
side-caller continuation PCs, zero/high-bit/missing results, all registers,
modeled comparison flags and exact ordered writes. Kernel tests additionally
cover stack-address wraparound. No pre-turn Doom source changed (747 files),
and no runtime or old instruction-semantics change was made.

Boundary: this is a wrapper contract, not a proof of the inner name search,
complete side-loader execution, successful startup or reachable aiming parity.
The original error function itself is also outside this milestone.

Next: prove the inner search's absent-texture (`-`) case and common restoration
path, then its table iteration/string comparison and memory frames. Feed those
actual paths back through the wrapper and the already-proved side caller.


## Complete no-texture lookup branch

`OriginalTextureDash` authenticates two additional original ranges:
`0x346f0..0x34700` and `0x34741..0x34747`. The first saves EBX, ECX, EDX,
ESI and EDI, copies the name pointer, then tests its first byte. The read occurs
after all five pushes. A leading `-` zeros EAX and jumps to the common restore;
another byte reaches the named-texture table-search entry at `0x34700`.
The restore reads the five saved registers and return word, preserving memory.

The prologue's stack readback, protected words above its saved registers, and
arbitrary separated-word preservation are proved with modular addresses.
`E1M1AimTextureDash.inner_path` composes the actual inner instructions in at
most 16 steps. `wrapper_path` supplies this path to the preceding wrapper proof
and returns to the caller's exact PC in at most 27 steps. It no longer assumes a
helper execution or its stack/memory frames for this branch. The register proof
restores every register except EAX (zero) and ESP (entry ESP plus four).
The complete wrapper word frame reduces to separation from its eight stack
writes at entry ESP minus 4, 8, 12, 16, 20, 24, 28 and 32.

Validation: 15 new public theorems; 7 new and 7 preceding-suite tests; 739 proof
build jobs; 2,860 strictly audited declarations; 68 authenticated ranges.
Independent Unicorn checks cover 128 complete dash successes (inner and
wrapped), 128 non-dash table-entry boundaries and 128 arbitrary common returns.
They check all registers, modeled flags, full mapped data and ordered writes,
including names overwritten by saved EDI. Kernel-checked concrete compositions
use the actual original code programs, including a wrapping stack; no synthetic
RET or name-search oracle is supplied. All 749 pre-turn Doom sources are frozen.

Boundary: the dash guard describes the byte actually read after pushes. Deriving
that condition from startup's original name bytes still requires their stack
separation. Named-texture iteration/string comparison, matched and exhausted
search paths, complete side-loader startup and reachable aiming remain open.
The generic common restore is ready for the exhausted-search path, but the
separate matched-search epilogue has not been connected here.

Next: cover table initialization and exhaustion, then the bounded name comparison
and table loop, reusing the saved-stack and wrapper composition results.


## Named-texture initialization and the first comparison

`OriginalTextureTable` authenticates `0x34700..0x34722` and
`0x3473c..0x34741`, including both original global-data relocations. It proves
that the count gate uses signed comparison against zero. A positive count
initializes ECX/ESI to zero, reads the first texture pointer, supplies the name
in EDX and eight-byte bound in EBX, and executes the actual CALL to `0x4198c`.
The pushed continuation is `0x34722`. A nonpositive count assigns -1 and
falls through to the previously proved common restore.

`E1M1AimTextureTable` connects both branches to the actual prologue. The first
comparison boundary takes at most 18 instructions from inner-function entry.
The nonpositive-count return takes at most 19 and is joined through the outer
wrapper's error branch in at most 26. Saved-register restoration reuses the
existing stack readback proofs; the full inner memory frame reduces to its five
explicit pushes. No helper execution or synthetic return premise remains for
these paths. The missing result is -1, distinct from the dash branch's zero.

The count is read after the prologue, and both table-pointer reads precede the
comparison CALL's stack write. The contracts retain aliasing and signed/high-bit
counts. They do not infer pointer validity, table size or data/stack separation
from reachable startup.

Validation: 14 new public theorems; 7 new and 7 preceding-suite tests; 741 proof
build jobs; 2,893 strictly audited declarations; 70 authenticated ranges.
Independent x86 checks cover 192 cases: 102 positive comparison entries and 90
nonpositive returns (46 continue to the wrapper error entry). All registers,
modeled flags, mapped data and ordered writes match, including count globals
modified by prologue writes and a texture-pointer cell overwritten by the later
CALL push. Kernel-checked compositions use original code, including a wrapping
stack. All 751 pre-turn Doom source files are unchanged.

Boundary: comparison execution, result handling, subsequent iteration and both
named-search matched/exhausted outcomes remain open. A nonpositive initial count
is covered; exhaustion after actual comparisons is not yet covered. `I_Error`,
complete loader startup and reachable-state aiming correspondence remain open.

Next: authenticate and prove the bounded name-comparison routine, connect its
result to the match/continue branches, and close the table loop using the saved
stack and return contracts already available.


## Original comparator byte folding

The authenticated range `0x41999..0x419b5` contains the two original ASCII
folding blocks and `CMP CL,CH`. `OriginalTextureFold` proves their bounded
executions, exact modeled flags, memory preservation, and lowercase results for
all 256 byte values. The two register writes preserve each other's byte; all
other registers remain unchanged. Lowercase is idempotent. No locale-dependent
or non-ASCII normalization is introduced.

`X86ByteRoutine` is an opt-in extension of the existing instruction interpreter:
register-direct byte CMP/ADD, register-to-register byte CMP, and short JA decoding.
An execution embedding theorem covers arbitrary old programs, states, exit sets
and fuel. Existing files, decoders and semantics are untouched. New arithmetic
flags model ZF/SF/OF/CF; this does not claim unmodeled flags or full CPU correctness.

Validation: 15 new public theorems, 7 new and 7 preceding-suite tests, 743 proof
build jobs, 2,922 strictly audited declarations and 71 authenticated ranges.
Independent Unicorn execution covers all 65,536 input byte pairs through the
original fold/compare blocks, plus 512 single-fold cases. Registers and modeled
flags match, and no memory writes occur. Tests reject altered authenticated
bytes and file mappings, and check decoder boundaries and old-program embedding.
All 753 pre-turn Doom sources remain unchanged. Python extraction/hash binding
and the instruction-semantics trust boundary remain explicit.

Boundary: individual original blocks are proved; the whole bounded comparison
call is not. The composed value theorem concerns the two result states and does
not yet prove the surrounding comparator loop. The prologue, byte loads,
equal/mismatch branches, length/zero termination, stack restore, caller join and
texture table loop remain open, followed by reachable initialization.

Next: connect the actual byte loads and fold/compare blocks to one complete
comparison iteration, then prove termination within the caller's eight-byte
limit and connect the real return to the texture lookup's match/continue branch.

## One complete original comparator iteration

`OriginalTextureIteration` authenticates `0x4198c..0x41999` and
`0x419b5..0x419ce`, retaining the separately authenticated fold/CMP range.
`iteration_execution` proves an actual instruction prefix from `0x41995` in
at most 20 instructions, reusing `cl_execution`, `ch_execution` and
`compare_execution`. There is no supplied comparator-execution hypothesis.
The exact result is one of:

- Folded bytes differ: EAX is their zero-extended 32-bit difference, EDX is
  the zero-extended right byte, and PC is `0x419cc`.
- Equal zero: EAX is zero, EBX and pointers other than EAX are unchanged,
  modeled flags are the final XOR flags, and PC is `0x419cc`.
- Equal nonzero: EBX decreases by one, EDX then EAX increase by one, all with
  32-bit wrapping, and PC is the loop-header TEST at `0x4198d`.

The loaded/folded value lemmas connect CL/CH to the actual memory bytes.
The iteration preserves memory and ESP. `restore_execution` executes actual
POP ECX and RET, reading both stack words. `first_iteration_return` composes
the original PUSH/TEST/JNE, one exiting iteration, and restoration in at most
25 instructions. `caller_return` reaches `0x34722` under its explicit incoming
return-word and stack-separation conditions. `table_first_return` specializes
that result to `OriginalTextureTable.comparison`, deriving the eight-byte bound
and pushed return word from the existing caller theorem. The first-exit
condition is still required; these are not arbitrary eight-byte termination.

No name/stack separation is silently introduced: the first loads read the
memory after PUSH ECX, so aliasing can change the compared names. The explicit
`Apart` premise protects the incoming return word. Concrete tests include a
wrapping stack and name bytes overwritten by this push.

`X86BytePrefix` adds path composition without changing prior semantics.
`X86ComparatorRoutine` decodes register DEC independently of PC and uses the
existing wrapping arithmetic projection. SUB/INC/DEC flags are forgotten;
branches use freshly established flags. The explicit semantics, empirical
independent x86 checks, and reachable whole-game obligations remain distinct.

Validation: 25 new public theorems; 7 new and 14 prior tests; 746 proof-build
jobs; 2,967 strictly audited declarations; 73 authenticated ranges. The strict
allowlist remains `propext`, `Quot.sound`, `Classical.choice`. Independent x86
executes all 65,536 byte pairs through one iteration and 256 complete calls
with bounds 0..8, including 64 stack/name alias cases. Complete-call checks
compare all registers, full mapped data and the ordered push write. These
complete-call tests extend beyond the universal theorem and are not promoted
to formal termination evidence. All 755 pre-turn Doom sources are unchanged.
Evidence is `artifacts/e1m1-aim-texture-iteration/validation.json`.

The following milestone discharges the comparator gate, repetition and complete
return obligations. Texture-search continuation and table iteration remain open.

## Complete bounded original texture comparator

`OriginalTextureComparator` completes the original routine, reusing
`OriginalTextureIteration.iteration_execution`, `restore_execution`, and the
existing prefix composition machinery without changing any prior Doom source.
The loop-header TEST/JNE either reaches the loads in two instructions or, for
zero EBX, reaches the common restore with EAX=0 in four instructions and no name
loads. A decreasing natural measure proves `(v-1).toNat=n` whenever
`v.toNat=n+1`; wrapping decrement at zero is never treated as descent.

`loop_execution` reaches the common restore in at most `22*n+4` instructions.
`complete_execution` includes actual PUSH ECX, repeated gates/iterations, actual
POP ECX and RET in at most `22*n+7`, for **every unsigned 32-bit initial bound**.
There is no first-exit or helper-execution premise. The exact endpoint `complete`
retains the full register/memory/flag state and reads the actual return word.
`complete_restoration` restores ECX, advances ESP to incoming ESP+4 and returns
to the incoming return word under explicit stack-word `Apart` separation.
`complete_frame` gives exactly the post-PUSH memory and unchanged EBP/ESI/EDI.

`complete_result` derives EAX's exact memory-byte specification from the original
loop: compare ASCII-lowercased bytes in order; return the difference of their
zero extensions at the first mismatch; return zero at equal NUL or exhausted
count. Pointer increments wrap. The specification reads **post-PUSH memory**,
not an assumed pristine string. Kernel tests include equal pre-PUSH names whose
actual comparison returns -97 after saved ECX overwrites a name. No host string
oracle or implicit name/stack separation replaces original execution.

`table_return` derives bound eight and return word from
`OriginalTextureTable.comparison_arguments`, completing the comparator in at
most **183** instructions to `0x34722`. `table_call_return` composes the actual
six-instruction table setup/CALL at `0x3471d` with the complete comparator in
one combined original-byte program: at most **189** instructions from `0x3470c`
to `0x34722`. The stack separation remains explicit; the former first-iteration
exit assumption is gone. The earlier table-CALL write also remains visible to
aliased name loads.

Validation: **18** new public theorems, **9** new and **21** prior tests,
**747** full proof-build jobs, **3,003** strictly audited declarations,
**73** authenticated ranges, **828** map cells and **475** pinned rows. The
existing byte ranges already cover this routine; no new extraction spec was
needed. Strict allowlist remains `propext`, `Quot.sound`, `Classical.choice`.
Independent x86 validation freshly reruns **65,536** iteration byte pairs and
**256** prior complete calls, plus **882** new complete calls including **85**
actual table setup/CALL/RET paths. The new set covers bounds 0..8, every bound-
eight mismatch/NUL position, **340** stack/name aliases, **170** wrapping-stack
and **170** wrapping-name cases, and **32** large-count early exits. All
registers, mapped memory and ordered writes match. These are empirical checks;
universal termination is supplied by Lean, not by extrapolating the test set.
All **758** pre-turn Doom files and **37** prior evidence files are unchanged.
Evidence: `artifacts/e1m1-aim-texture-comparator/validation.json`.

Limits: explicit instruction semantics, not CPU/hardware refinement; forgotten
SUB/INC/DEC flags remain unknown. Python extraction/mapping/hash binding remains
a trust boundary. The full runtime/game test suite was not run. The complete
comparator is proved, but not a whole named-texture lookup or reachable startup.

Next: authenticate and join `0x34722` match/continue handling, matched-search
restoration, and the texture-table loop including exhaustion after comparisons.
Reuse the complete comparator and existing stack contracts. `I_Error`, full
side-loader control flow, reachable initialization, and whole-game observable
correspondence remain open.

## Complete positive named-texture search and wrapper

`OriginalTextureSearch` authenticates the 26 bytes at `0x34722..0x3473c`, including
its count-load relocation. TEST/JNE selects the actual comparison result;
matched return moves ECX to EAX and executes five POPs/RET. Mismatch reloads the
count, increments ECX/ESI, compares signed values, and either repeats at
`0x3470e` or assigns -1 and executes the common restoring return. The existing
comparator is reused unchanged on every iteration. No first-exit, helper-body,
or successful-search execution is supplied as a premise.

Each subsequent setup/CALL/comparator/RET takes at most 188 instructions, and a
complete search round at most 202. Repetition uses a natural measure toward
INT_MAX rather than the mutable count cell. Starting at ECX=0, signed JL cannot
continue after the increment reaches INT_MAX, even when stack writes alter the
reloaded count. The conservative universal bound is `202*2147483647`, not a
claim about small-table performance. A separate return theorem proves actual
RET, original saved return PC, ESP+24, and EAX=-1 or a nonnegative texture index.
The continuation predicate is distinct from endpoint PC: a real return address
is allowed to equal the loop header.

Comparison semantics retain the exact two writes: CALL stores `0x34722` at
ESP-4; comparator PUSH stores ECX at ESP-8. Names are compared in that memory,
and later count/table reads also see it. `search_frame` preserves words apart
from those slots. `search_saved` restores the five saved registers and preserves
EBP on matched and exhausted exits, including wrapping stacks.

`E1M1AimTextureSearch.named_execution` joins the real prologue/name branch/count
gate/ESI initialization to the complete search and RET. Its explicit conditions
are non-dash name and positive count in the actual post-prologue state.
`named_return`, `named_above`, and `named_registers` restore the original return
PC, ESP+4 and all other registers except EAX while protecting upper stack words.
`wrapper_execution` joins the real wrapper CALL and complete named lookup to
its result gate: success executes the caller return; exhaustion executes into
**the wrapper error arm at `0x34760`, before I_Error is called**. It does not
assume success or claim execution of I_Error's body. The bounds from lookup and
wrapper entries add 13 and 24 instructions respectively. Both programs are
embedded into one agreeing byte-instruction program without changing old code.

Validation: 36 public theorems; 9 new and 53 prior passing tests; focused build
703 jobs and full proof-target build 749 jobs. Cumulative certificate strictly
audits 3,076 declarations with 74 authenticated ranges, 828 map cells and 475
pinned rows. Allowlist remains `propext`, `Quot.sound`, `Classical.choice`.
Independent CPU checks execute 259 new cases: 144 repeat comparisons, 135 match,
124 exhaust, 86 start at the wrapper, 90 alias, 42 wrap the stack, and 42 change
the reloaded count. All registers, mapped memory, ordered writes and modeled
final flags match. The prior 65,536 byte pairs, 256 earlier complete calls and
882 comparator calls are freshly rerun. Negative byte/mapping/audit/guard
mutations fail. All 759 baseline Doom files and 38 predecessor evidence files
are unchanged. Evidence: `artifacts/e1m1-aim-texture-search/validation.json`.

Limits: explicit instruction semantics, not hardware refinement. Initial
positive/named guards have not been derived from reachable startup. Prior
leading-dash and nonpositive-count paths remain separate; a unified all-branches
API is not yet assembled. No actual side-loader call/iteration was joined here.
The full runtime/game test suite was not run. This is not startup completion.

Next: embed the three real `OriginalSideTextures` calls/returns (continuations
`0x2e483`, `0x2e494`, `0x2e4a5`) into byte-prefix semantics, combine all lookup
branches, establish pinned texture-catalog/name facts rather than assuming
success, and compose side writes/pointer emission/loop iterations. Continue
actual map/actor initialization, placement and preservation into aiming. Only
allocation facts needed by those startup obligations are in scope; I_Error,
reachable initial-state correspondence and whole-game parity remain open.

## All-branch texture lookup and an actual side-loader body

`E1M1AimTextureLookup` combines leading dash, initially nonpositive signed count,
and complete positive named search into one execution from `0x346f0` through
real RET. Dispatch uses the actual post-save name and count, retaining aliases.
The bound is `202*2147483647+19`; saved return word and outside-epilogue return-PC
conditions remain explicit and are derived for the actual callers. Register
restoration, upper-stack words and arbitrary protected word frames are proved.
Its wrapper executes from `0x34750` through the real inner CALL, lookup, result
gate and either caller return or **error arm `0x34760`, before I_Error is called**.
The wrapper bound is `202*2147483647+30`; no success/helper-path premise is needed
for execution. No I_Error call/body or fabricated normal return is claimed.

`E1M1AimSideLookup` joins unchanged old caller blocks and the lookup using proved
program agreements and explicit old-run embedding into byte-prefix semantics.
`execution` starts at `0x2e47e`, follows actual returns `0x2e483`, `0x2e494`,
`0x2e4a5`, and executes scratch/halfword stores between calls. A failed lookup
ends at the error arm after the first, second or third field; three successful
calls reach `0x2e4af`. Execution is unconditional on lookup success.

`Returned` records success of the computed calls; it remains an explicit
condition for success-only register/frame/input conclusions. It is NOT pinned
catalog success, and must still be derived from initialized memory. `Safe`
protects a word from the actual stack footprint (ESP through ESP-44) and the
three halfword writes. `post_input` derives the suffix Input from incoming Input,
Returned and Safe for the source sector field and sector-base global, instead
of assuming the reached post-texture image. `emitted` then supplies the actual
sector-pointer bytes using the unchanged SideEncoding/SideAdvance theorems.

`iteration_execution` extends the three-call path through pointer emission and
the signed loop latch, reading the actual post-write count. `body_execution`
adds the seven offset-load/store/setup instructions from `0x2e46a`; its bound is
`3*(202*2147483647+30)+36`. It proves one complete body ending in error, next-body
entry or cleanup boundary, not repetition or loader entry/cleanup execution.

Final recovered validation: **32** public theorems; **8 new + 85 prior = 93**
tests freshly passing in four bounded batches; **705** focused / **751** full
proof-target build jobs. The final cumulative certificate and a separate Lean
invocation/strict audit pass with **3,143** declarations, **74** inherited
byte-authenticated ranges, 828 map cells and 475 pinned rows. Existing ranges
already cover the composition. Byte, mapping, audit and dropped success/frame/
source guards are rejected. Allowlist remains `propext`, `Quot.sound`,
`Classical.choice`; no new sorry/axiom/native_decide/bv_decide. Original TDD logs
are retained. All **761** pre-milestone Doom files and **34** predecessor evidence
files remain unchanged against the original manifests. Evidence:
`artifacts/e1m1-aim-texture-lookup/validation.json` and final `recovery-*` logs.

Fresh independent CPU validation covers **417** connected cases, **209** from
offset loads, **135/126/478** dash/nonpositive/positive lookup invocations,
**89** complete three-call paths, and errors after first/second/third fields
**208/96/24**. It includes **128** alias and **64** wrapping-stack cases,
**44** continuing and **45** finishing bodies. All registers, mapped memory,
ordered writes and modeled final flags match; maximum 17,199 instructions.
Inherited checks freshly rerun 259 searches, 882 comparator calls, 65,536 byte
pairs and 256 earlier complete calls. These remain empirical CPU checks, not
universal termination or hardware refinement. SUB/INC/DEC flags remain forgotten.
The full runtime/game test suite was not run.

`catalog.json` authenticates host WAD extraction: **125** textures, **648** sides,
**1,944** fields (**1,331** dash / **613** named), and **33** unique names including
dash, all with host first-match IDs. **33** CPU cases use those names in a
constructed catalog image. This is not DOS `R_InitTextures` execution, reached
pointer-table/image representation or a Lean theorem of named lookup success.

Next: prove pinned catalog/name success and relevant memory stability at actual
calls; compose all side bodies while preserving earlier pointers, source fields
and globals, including the count after stack/field/pointer writes. Reuse
SideAdvance's bounded branch and pointer frames, SideEncoding, and the completed
475-row line loop. Then discharge loader entry/allocation/cleanup, map/blockmap/
actor initialization, actual placement and list order, and preservation into the
production `Engine.start` relation. `DosStartup` allocateOnly/forget lifecycle
facts do not initialize payload bytes. Startup and whole-game correspondence
remain open; continue without milestone approval.

## 2026-10-20 recovery checkpoint: one-image side loop through selected cleanup

The previous catalog/loop plan append was interrupted by an approval/session
lease failure. It was not claimed as written. After renewed user authorization,
this section records the actual current checkpoint and supersedes the older
“next” list immediately above. Prior implementation and evidence were preserved.

The completed catalog first-match proofs and 648-body one-image loop remain
unchanged (`E1M1AimTextureCatalog`, `E1M1AimPinnedCatalog`, `E1M1AimSideLoop`,
`E1M1AimPinnedSides`). The loop derives every actual helper call/return, branch,
source image and iteration invariant from one incoming image plus static regions.
Pinned WAD evidence includes 648 sector indices, 125 texture names, 33 queries
and 1,944 ordered texture fields. This is conditional memory representation, not
execution of R_InitTextures or WAD caching.

New `E1M1AimSideStack` protects all upper-stack windows ESP+4 through ESP+35
through that entire loop. `OriginalSideCleanup` executes actual cleanup and a
selected Z_Free branch: valid signature, owner>256, owner-cell clear, header
user/tag/signature clears, both adjacent user fields nonzero after the actual
writes, actual callee RET and actual caller epilogue/RET. Full cleanup bytes
`0x2e4dd–0x2e4f0` and full 144-byte Z_Free `0x39600–0x39690` are authenticated;
error, unowned and coalescing branches are **not** thereby proved.

`E1M1AimSideCleanup.execution` composes the complete byte execution from
`0x2e46a` to the final caller return. `cleanup_ready` derives all free conditions
from a single incoming `Image` and regional `Placement`; no reached Ready or
assumed callee execution appears in the composite input. The image explicitly
states header owner, owner cell=raw, valid signature, links and occupied neighbors.
`cache_owned` preserves the initial owner-cell/raw relation through all bodies.
`Placement` protects metadata from loop writes/PUSHes and protects output/lower
stack/upper stack/link reads from actual deallocation writes. `observations`
proves all 648 sector pointers, six restored caller registers, ESP+36 and the
original caller return PC. These conditions **do not prove original heap history,
actual cache-table identity, or reachability of the busy-neighbor branch**.

Evidence: `artifacts/e1m1-aim-side-cleanup/validation.json`:
- 28 public theorems; 3,327 strictly audited declarations; 76 unique authenticated
  ranges (74 inherited plus the two cleanup ranges).
- Focused build 713 jobs; full proof-target build 758 jobs.
- 118 distinct passing tests: 8 cleanup and 110 predecessor tests, bounded batches
  33/32/21/32. Byte/mapping/relocation/audit and omitted initial/placement/upper/
  raw-pointer guards reject. The default-recursion import failure is retained;
  its limit10000 rerun passed.
- Separate cumulative certificate, separate Lean invocation and strict axiom audit
  passed; allowlist propext/Quot.sound/Classical.choice only.
- Independent CPU: 128 selected-branch local runs check all registers, ordered
  writes, mapped memory and modeled CMP flags. Aliases into upper or callee saved
  words test actual semantics but are excluded by the composite Placement.
- One uninterrupted 648-body + cleanup + caller RET run: 1,944 lookup IDs,
  1,549,745 instructions including 33 cleanup instructions; checks complete output,
  all previous records/inputs at headers, saved stack and exact cleanup memory.
  This is a constructed fixture, not reached initialization. Final ADD ESP flags
  are forgotten by the model.
- All 767 pre-milestone Doom sources and 71 predecessor evidence files unchanged;
  all 769 recovery-snapshot Doom sources and 9 interrupted milestone files also
  unchanged. No prior baseline was replaced. Runtime/game suite was not run.

Next-entry work has begun as **reconnaissance/empirical execution, not a new Lean
entry theorem**. `next-entry-recon.json` authenticates entry/gate/length/cache/cached/
tag ranges and records an actual 30-instruction CPU prefix from `0x2e3e0` through
W_LumpLength to before Z_Malloc `0x39690`, on constructed lumpinfo memory. Pinned
SIDEDEFS index9 of1264 has length19440: count648, allocation bytes11664, tag50,
owner0, return0x2e415. It does not execute allocation, memset, caching or reading.

Continue automatically with actual length/table frames, relevant allocator
execution, side publication and memset, W_CacheLumpNum miss/hit paths and actual
raw ownership. The cache owner slot comes from `[0x74f94]+4*index`; cache miss
calls allocation/read, cache hit calls Z_ChangeTag. Establish adjacent occupancy
from real placement/history or extend cleanup to the coalescing branch actually
needed. Derive gate-to-loop Incoming through the ESP+4 save. Then execute catalog,
raw-map/blockmap and actor initialization and preservation into production
Engine.start. Reuse the completed 475-line loop and relevant grouping heap/frame
proofs. Preserve actor identities and exact list order/RNG/filter behavior.
Startup completion still requires continuous original-boundary execution yielding
the actual image/placement/tables/stamps relation, without hidden success, reached
image, helper-path or Kept assumptions. See the updated `SESSION_HANDOFF.md` for
exact APIs, commands and outstanding obligations.

### 2026-10-20 — real side entry through first-free selected allocation

The preceding reconnaissance has become a kernel-checked connected prefix.
`E1M1AimSideEntry.execution` runs the actual entry at0x2e3e0, W_LumpLength and
request arithmetic in30 steps to0x39690. Initial directory facts and explicit
prologue/CALL/PUSH separation derive the signed length branch,19440 bytes,
count648, request11664/tag50/owner0 and saved return0x2e415.

`E1M1AimSideAllocate.execution` continues from that exact state through actual
allocator saving/preparation, first-free selection, split OR no-split, metadata
commit, POPs and RET. It yields a prefix≤90 steps, PC0x2e415, EAX=v.block+24,
ESP=initialESP-32. Initial heap view/static separation remain boundary assumptions;
no reached allocator image or successful helper premise is supplied. Both previous
block choices are covered. General searching/purging and actual prior heap history
are not claimed. Existing decoders are unchanged; opt-in X86StartupRoutine adds
unsigned register DIV with zero/overflow rejection and undefined flags forgotten.

The contract deliberately does not claim all later input preservation: count,
restored ECX9 and upper saved words still need allocation write frames before
publication/memset/cache. A fixture checking them is not a universal theorem.
The earlier full648-body loop/cleanup remains unchanged and **not yet connected**
to this entry segment.

Validation, recorded in `artifacts/e1m1-aim-side-entry/validation.json`:
- 25 public proof/infrastructure contracts;3478 strict audit entries,3460 distinct
  declarations,85 unique authenticated ranges. Duplicate inherited audit segments
  are not silently counted as distinct declarations.
- 6 focused +43 side-predecessor +35 allocator-predecessor tests =84 passed.
  Byte/data/mapping/relocation/audit/guard negative mutations reject.
- Full proof-target command from scripts/test:761 jobs passed. Separate generated
  certificate Lean invocation and strict allowlist audit passed.
- 64 uninterrupted CPU entry/length/allocation/RET fixtures:32 split,32 unsplit,
  both predecessor choices, alignments0..3, excess0/64/65/4096 and wrapping stacks.
  Checks registers, full mapped data, ordered writes, modeled flags, actual request,
  instruction counts and return. Constructed placement, not startup reachability.
- Original770 Doom-source and37 cleanup-artifact hashes unchanged;23 allocator
  predecessor evidence hashes unchanged. No runtime changes; game suite not run.
- RED/build/debug logs retained. An owned timed-out entry probe was found and
  terminated; final handoff verifies no orphan process.

Next work is concrete: preserve count/index/saved stack, publish side base, execute
memset0x3fe70 and its actual helpers0x418e0/0x41917, execute cache miss/hit and
raw read, then derive gate-to-loop Incoming/UpperStack. Authenticated new helper
reconnaissance is in `next-zero-cache-recon.json`, outside the85 proof ranges.
W_ReadLump's disk-icon and file seek/read calls require an explicit environment
boundary, not a hidden filesystem-success premise. A cache allocation that splits
leaves a free immediate remainder; absent actual intervening occupancy, cleanup
must handle next-neighbor coalescing. The current busy-neighbor theorem cannot
silently cover it. Actual R_InitTextures, raw-map/actor construction and production
Engine.start relation remain open. **This checkpoint is not initialized startup.**

### 2026-10-20 — allocation frames/publication recovered; real nested memset CALLs

The interrupted `E1M1AimSidePublish.lean` has been preserved unchanged and fully
validated. It derives count648, ECX9, allocator-restored EBP/ESI/EDI and protected
caller saves through the actual selected split/no-split allocator. Static address
frames are explicit; no reached preservation image is assumed. Its ten-instruction
publication suffix writes the side base and CALLs memset at0x3fe70. Connected
entry takes≤100 steps, with EAX=block+24, ECX9, EDX0, EBX11664, ESP=initial-36 and
saved return0x2e437. `published_count`/`published_base` include their true guards.

`E1M1AimSideMemset` now executes the real9-instruction memset wrapper, including
EAX/ECX saves, DH/DL moves and shifts, and the8-instruction aligned helper path.
The second nested CALL reaches0x41917 with ECX2916, EDX0, EAX=block+24 and
ESP=initial-56. `execution` connects that exact state to entry0x2e3e0 in≤117 steps,
under the previous initial directory/heap/frames and explicit4-byte destination
alignment. The state is composed from the instructions, not supplied at a seam.
Frames preserve count, published base, upper saves and arbitrary protected words
using original addresses. Actual earlier heap/directory construction is still open.

The opt-in `X86FillRoutine` adds register8A/8B MOV, OR, byte-memory CMP, TEST AL
and prefix/lifting lemmas; old interpreters remain unchanged. It deliberately does
not yet implement DEC/ROR or partial-known shift flags. The word-filler body,
universal zero-output and helper-return theorems are **still open**. In particular,
SHR count2 defines ZF/SF/CF but not OF: do not invent OF=false to fit the old full
flag structure. Use a justified partial flag projection/consumer when continuing.

Evidence:
- `artifacts/e1m1-aim-side-publish/validation.json`:11 public contracts,3500 audit
  entries/3482 distinct,85 authenticated ranges,64 actual CPU publication cases.
- `artifacts/e1m1-aim-side-memset/validation.json`:12 new proof+3 infrastructure
  contracts,3530 strict audit entries/3512 distinct,87 Lean-authenticated ranges.
  Word filler0x41917..0x41983 is a separate authenticated **CPU-only** range.
-96 distinct tests passed (12 final focused,22 connected,35 allocator,27 other
  side predecessors), including byte/mapping/relocation/audit and missing
  frame/alignment/word-protection guards. Both cumulative verifiers and separate
  independent Lean/strict audits passed; full proof-target build764 jobs.
-512 uninterrupted independent CPU entry→memset-return cases cover32 address
  offsets, both previous-block choices, split excess0/64/65/4096, ordinary/wrapping
  stacks. All registers, ordered writes, mapped data, saved stack/count/base,
  actual nested CALLs/RETs and11664 zero bytes checked.128 aligned cases also
  check the formal17-step nested suffix.5228..5291 instructions per case.
  **Full memset zeroing/return is empirical evidence, not a universal theorem.**
- Original773 Doom+38 evidence hashes, recovery783-file snapshot and nested793-file
  preturn snapshot unchanged. Original RED/GREEN logs and baselines preserved.
  One test invocation used a nonexistent allocator module; the corrected35-test
  batch passed. Failed build/test logs retained. No runtime changes/game tests.

Continue from the exact `nested s` at0x41917 with symbolic word-fill blocks/loops,
static payload-vs-stack/metadata separation, zeroed-byte coverage and all actual
RET frames. Then actual cache/read, gate-to-loop, catalog/raw-map/actor startup and
Engine.start relation remain as listed above. A split cache block's free remainder
still requires coalescing or a proved intervening occupied neighbor; the old
busy-neighbor cleanup theorem does not silently apply. **No startup completion.**

### 2026-10-20 — symbolic word groups, honest partial flags, complete32-byte case

`E1M1AimWordFill` now proves universal2916-word/11664-byte zeroing and all three
nested RETs, composed from actual original entry0x2e3e0 to0x2e437 in≤5240steps,
**for explicitly32-byte-aligned destinations**. The stronger alignment is stated
in the new theorem name/signature; the earlier4-byte prefix is unchanged. This
is a useful verified subset, **not completion of the requested all4-byte-aligned
memset theorem**. Leading0..7 alignment words and nonzero1..3-word tails remain
open. No cache/gate or initialized-startup progress is claimed by this checkpoint.

The new opt-in `X86WordFillRoutine` uses a legacy/zero-only flag sum. SHR2 retains
ZF without giving OF any Boolean value; SF/CF are conservatively forgotten.
JE/JNE use known ZF, unknown signed/carry consumers fail closed. DEC correctly
preserves known CF while setting its defined ZF/SF/OF. Old interpreters and proof
contracts are unchanged, with a checked exact prefix embedding.

The central16/32-byte groups are proved symbolically: actual14-instruction pair
body, arbitrary-count induction with descending-counter guards, both terminal
branches, exact cursor/register/memory summaries and universal byte zeroing.
Actual PUSHes derive saved count/index/base/return words, static output-vs-stack
separation protects them, and11 original POP/AND/JE/RET instructions return all
the way to0x2e437. `entry32_execution` connects the earlier actual entry prefix;
`entry32_nested_frame`, count/base/upper frame theorems protect earlier state with
explicit original-address output separation. No reached helper-success or saved
memory image premise is hidden in the complete32-byte theorem.

Evidence `artifacts/e1m1-aim-word-fill/validation.json` and `report.json`:29 proof+
3 infrastructure contracts,3593 strict audit entries/3575 distinct,88 authenticated
ranges (word filler now Lean-bound).108 distinct final tests passed; full proof
build766 jobs; separate certificate rerun and strict audit passed. Independent
CPU reran512 whole-prefix cases, including16 with the32-byte destination covered
by the new theorem, plus1472 DEC/SHR2 flag cases. Undefined SHR2 OF is never fixed
or compared. Prior Doom sources/evidence are preserved; no runtime/game tests.

Next: derive head alignment from original4-byte alignment; generalize saved-count
setup for2909..2916 remaining words; reuse the proved group induction; execute
nonzero word tails and preserve already-zero head bytes across the actual count
PUSH. Then compose the existing returns for every4-byte destination. Later cache
read/environment, free-remainder coalescing, gate/648-loop and actual catalog/raw
map/actor-to-Engine.start obligations remain unchanged. **Startup incomplete.**

### 2026-10-21 — interrupted all4-byte-aligned memset recovered and completed

`E1M1AimWordAligned.entry_execution` now proves actual original execution from
0x2e3e0 through length/allocation/publication and the ENTIRE nested memset to
0x2e437 in≤5300instructions, with every11664 output byte zero for every explicitly
4-byte-aligned destination. The stronger32-byte restriction is gone from the new
contract; its predecessor remains unchanged. The head witness h<8 is derived
from low5 initial address bits, never supplied as reached alignment or an image.

The actual0..7 head stores, post-head remaining-count PUSH/SHR2/setup, unchanged
symbolic group induction and both terminal branches, actual POP/AND/0..3 tails,
and all3RETs are joined at exact states. Static original-address separation
justifies PUSH/zero-prefix commutation for the memory summary, without reordering
execution. Saved POP values are derived. The3-word residual path honestly leaves
ECX1 until caller restoration. Entire memset-return registers and arbitrary
protected words, count/base/upper caller frames are proved. No old interpreter,
flag semantics or theorem was weakened; no new axioms or unchecked proof tactics.

Evidence `artifacts/e1m1-aim-word-aligned/validation.json`:32 new contracts,
3658 strict audit entries/3640 distinct,88 authenticated ranges.116 distinct
final tests passed (32 focused,22 connected,35 allocator,27 side predecessors),
including alignment/late-PUSH/saved-count/frame guards and byte/map/audit negative
mutations. Separate Lean/strict audit passed; full proof-target build767jobs.
Independent CPU reran512 entire-prefix cases, including128 four-byte-aligned cases
covering all8 heads/all4 tails (16also32-aligned), plus1472 DEC/SHR2 checks.
These remain constructed placements; undefined SHR2 OF is not assigned/compared.
Original835-file interrupted baseline, RED/failure evidence and all predecessor
Doom/evidence hashes preserved; only documented scripts/test and handoff/plan
old edits. No runtime/game validation claim.

The proof stops0x2e437. Authenticated follow-up disassembly in
`next-cache-call.json` identifies MOV EDX1, MOV EAX,ECX, XOR EBP,EBP, then
CALL0x38d00 at0x2e440 with return0x2e445. This4-instruction extension is NOT yet
proved; its originalESP-36 PUSH slot is already included in Entry32Safe, enabling
an explicit zero-output preservation argument. Then cache owner=[0x74f94]+36,
raw19440 tag1 allocation/read/environment, free-remainder coalescing, gate/648-loop
and actual catalog/raw-map/actor-to-Engine.start remain open. **This is the
completed all4-byte memset checkpoint, NOT startup completion.**

### 2026-10-21 — original-state cache CALL, dispatcher and connected helper requests

`E1M1AimCacheCall.entry_execution` extends the complete aligned memset by the
actual four instructions0x2e437..0x2e445, reaching W_CacheLumpNum0x38d00 in≤5304
steps from original entry. EAX9/EDX1/EBP0/ESP=originalESP-36 and return0x2e445
are derived. Original Entry32Safe slot6 protects every11664 zero byte from the
real CALL write; no reached zero image is supplied.

`E1M1AimCacheDispatch.entry_execution` executes the dispatcher in≤5317 total
steps. It computes owner=originalCacheTable+36 and branches according to the
preserved ORIGINAL owner-cell value. Both hit/miss branches are retained. Under
original cell=0, `miss_entry_execution` executes the real second W_LumpLength
CALL, all11 admitted helper instructions including RET, and actual Z_Malloc
CALL, reaching0x39690 in≤5331 total steps with19440/tag1/owner and return0x38d41.
Under original cell≠0 plus protected original signature, `hit_entry_execution`
executes the real signature CMP/JE and Z_ChangeTag CALL to0x399b0 in≤5322steps,
with the original raw pointer, tag1 and return0x38cd3. Neither helper is assumed
to return, and neither branch is claimed as the pinned preceding-startup history.

All11664 zero bytes survive dispatcher and either request. Original-address
`ReadSafe` predicates derive directory/cache reads from the same Initial and
preceding execution. `request_allocation_frame` preserves arbitrary protected
PRODUCED first-allocation metadata, equating the request memory to the actual
old allocated state; it does not invent or assume a new heap view. All preceding
modules, interpreters, theorem contracts and evidence are unchanged.

Evidence `artifacts/e1m1-aim-cache-call/validation.json`:31 new contracts,
3724 strict audit entries/3706 distinct,90 authenticated ranges.125 distinct
tests passed, including missing guards and byte/map/relocation/audit mutations;
independent Lean replay/strict audit passed; full proof build769jobs. Independent
CPU executed384 uninterrupted original-entry cases:128 miss,128 valid hit,
128 bad signature (the latter empirical only). All registers, ordered writes,
complete mapped data, zero output and produced allocation metadata checked;
all8 alignment heads/all4 word tails and wrapping/unaligned stack represented.
Caller/signature flags checked; miss final unknown flags not compared. The
fixtures are constructed placements, not actual earlier cache/heap history.
949-file baseline preserved except intentional scripts/test and handoff/plan;
no runtime/game tests or runtime source edits.

Next derive the actual next heap from preceding allocation plus the new frame,
with explicit original capacity/adjacency and split/no-split cases. The original
11664 side-allocation capacity does not imply successful raw19440 allocation.
Execute owned allocation (owner=cache+36), cache W_ReadLump CALL and explicit
filesystem/environment boundary; complete tag1 helper/epilogue on the genuinely
conditional hit path. Cache split leaves free remainder: occupied-next cleanup
still requires real occupancy or coalescing proof. Actual return/gate0x2e445..
0x2e46a,648-loop join and catalog/raw-map/actor-to-Engine.start remain open.
**This is a verified cache-request checkpoint, NOT initialized startup.**

### 2026-10-21 — produced next heap, actual owned raw allocation and read CALL

`E1M1AimCacheHeap` derives the second heap view from the exact ordered writes of
preceding side allocation and the preserved produced-memory frame. Both first
split/no-split branches are retained. First split produces its free remainder;
first no-split explicitly requires ORIGINAL free-successor owner/size/backlink/
next-link words and their frames. No arbitrary reached view is assumed. The
additional raw capacity is rounded19440≤nextView.size (signed); capacity for the
first11664 request alone is insufficient, with a kernel-checked counterexample.
These remain explicit local heap boundary conditions, not pinned startup history.

`E1M1AimCacheAllocate.entry_execution` runs from the same original0x2e3e0 through
side allocation, all zeroing, original-cell cache MISS, length CALL and real owned
raw allocation, BOTH second split/no-split outcomes, owner publication, tag1,
signature, four POPs and RET0x38d41 in≤5400steps. Owner is cache+36, not sentinel2.
`E1M1AimCacheRead.entry_execution` then executes the real cache loads/MOV/CALL to
W_ReadLump0x38bf0 in≤5404steps: index9, raw=nextView.block+24, ESP=originalESP-56,
actual return0x38d50. Restored ECX/ESI and pointer reads are derived through actual
saves/stores. The local helper view record is discharged from original History/
Conditions, never an original-entry success premise.

Exact second metadata, every assigned raw header/owner word through read CALL,
protected produced first-allocation words, and all11664 zero bytes are proved.
Byte-level output guards do not spuriously extend into the adjacent raw header.
No loaded raw payload follows from allocation: independent CPU confirms it stayed
unchanged. TEST-owner flags survive even though POP restores EDI to another value.
All old Doom sources, interpreters and theorem contracts remain unchanged.

Evidence `artifacts/e1m1-aim-cache-heap/validation.json`:30 new public contracts,
3785 audit entries/3767 distinct,90 inherited authenticated ranges (no new ranges),
132 distinct tests, separate Lean/strict audit, full proof build772jobs PASS.
384 uninterrupted CPU original-entry→W_ReadLump-CALL fixtures cover both first
predecessor choices, first no-split0/no-split64/split, raw extras0/64/65/4096,
all8 heads/all4 tails and wrapping/unaligned stacks. All registers, complete mapped
memory, ordered writes, both headers, owner, count/base, upper stack, zero output,
unchanged raw payload and defined flags checked. Fixtures are constructed, not
reached earlier DOS heap/cache history. Original821-file baseline preserved except
intentional scripts/test and handoff/plan; runtime/game suite NOT run.

Exact next: actual read prologue0x38bf0→disk-icon CALL0x38c26→0x1adb0;
original stack guards must extend to-76/-80. Directory handle/reopen choice,
seek0x408c0/read0x40935/optional close0x40902 and I_EndRead0x1aea0 remain explicit
unproved environment/helper boundaries. No successful helper or payload image is
hidden. Conditional HIT still stops at the prior tag1 request0x399b0; its actual
short tag branch/cache epilogue remains next connected work, never a convenient
replacement for miss history. Cache return/gate0x2e445..0x2e46a and existing648-loop
join remain open. Raw split leaves a free neighbor, so cleanup needs actual
coalescing or reached occupancy. Catalog/raw-map/actor/Engine.start linkage remains.
**This is a verified owned-allocation/read-CALL checkpoint, NOT startup completion.**

### 2026-10-21 — actual read prologue, disk gate/zero return and file requests

Three opt-in modules leave all preceding Doom/interpreter contracts unchanged.
`E1M1AimReadPrologue.entry_execution` runs the same original0x2e3e0 execution
through the owned raw allocation and actual W_ReadLump prologue to the real
I_BeginRead CALL0x1adb0 in≤5419steps. Five PUSHes, count guard, EDI9, EBPraw,
ECX=180+table, ESP=originalESP-80 and actual return0x38c2b are derived.
Original-address conditions protect the directory and all new stack slots;
old guards through-72 do not imply new-76/-80 separation.

`E1M1AimDiskRead.entry_execution` then executes three actual PUSHes and the
CMP/JE using ORIGINAL[0x29134]. Both outcomes remain: nonzero reaches0x1adc0
with ESPoriginal-92; zero executes three POPs/RET to0x38c2b with ESPoriginal-76.
The combined bound5428 includes both. No disk-icon return is assumed, and zero
is NOT promoted to actual earlier video history. Protected-word/byte frames
and exact ordered-write memory equalities preserve the preceding produced state;
prologue zero-output preservation is explicit and later byte-frame lemmas carry
any protected zero/raw byte. Raw19440 remains uninitialized/unloaded.

`E1M1AimReadRequest.entry_execution`, explicitly conditional on ORIGINAL icon
flag0, continues through the actual directory handle branch. Original handle=-1
pushes0x200 and the protected original filename pointer, CALL0x40691 with return
0x38c44/ESPoriginal-88; other handles supply EAX=handle/EDX=original directory
position/EBX0 to actual seek CALL0x408c0 with return0x38c70/ESPoriginal-80.
Total≤5436steps. Neither wrapper/DOS success nor a loaded payload is supplied.
The file-input guards protect original handle/offset/name through both heap
writes, zeroing, prologue and icon saves, including name read after mode PUSH.

**New actual scope boundary:** pinned-EXE reconnaissance finds earlier video
MOV EBX1 at0x1a021 and store[0x29134],EBX at0x1a041. Reachability of that earlier
code is open, but choosing the zero flag as startup history would be unjustified.
The nonzero icon body starts0x1adc0, first OUT0x1adc7 and IN0x1addf, with VGA
registers, aperture/latch effects and two copy loops. It needs explicit justified
device semantics/frames, not ordinary flat-byte copying or an assumed RET.
The zero-only file result is a useful conditional component, not avoidance of
this active branch. `next-boundaries.json` authenticates this discovery but is
reconnaissance, not a new formal execution certificate.

Seek INT21/AH42 is0x408d9; open wrapper0x40691 calls0x406b0 and reaches actual
INT21/AH3D0x406e0. Read0x40935 first calls handle-metadata helper0x4289d; binary
flag0x40 uses INT21/AH3F0x40985, text path0x409b9 filters CR/0x1a and can loop.
Descriptor bounds/vector[0x1f7ac]/[0x1f800], small-handle helper0x427f8, partial
register operations, CF capture RCL/ROR, error paths and genuine file-resource
position/bytes transitions remain. W_ReadLump uses signed JGE against directory
length, NOT equality. Optional close and active I_EndRead, five POPs/RET, cache
return/gate/648-loop join remain open; tag1 hit is unchanged at0x399b0.

Evidence `artifacts/e1m1-aim-read-prologue/validation.json`:39 new contracts,
3866 strict audit entries/3848 distinct,92 cumulative authenticated ranges
(90 inherited+187-byte read and240-byte icon ranges). Binding the full icon
bytes does NOT mean unsupported hardware instructions execute.107 distinct
final tests PASS, including missing disabled condition, six guards, byte/map/
relocation/audit mutations and fail-closed OUT/INT checks. Independent separate
Lean/strict audit and full775-job proof build PASS; no new proof warnings.
1152 uninterrupted independent CPU original-entry fixtures:384 active flag,
384 zero existing handle,384 zero reopen, all allocation cases/alignment heads/
tails and wrapping stacks. All registers, ordered writes, complete mapped data,
zero bytes, unchanged raw payload, produced metadata/count/base/upper stack and
defined flags checked. No synthetic helper returns, interrupt effects or PC
patches. Constructed placements are not pinned preceding DOS history.
826-file baseline (784 Doom,39 prior evidence,3 intentional-edit files) preserved
except scripts/test and handoff/plan. Runtime/game suite NOT run.

**This is a verified partial read/disk/file-request checkpoint, NOT a full read,
cache-return proof or initialized startup.** Continue at the explicit active VGA
and DOS/file resource interfaces, retaining all inherited heap/history/capacity
conditions. Free-remainder cleanup, catalog/raw-map/actor and Engine.start
linkage remain separate open obligations.


