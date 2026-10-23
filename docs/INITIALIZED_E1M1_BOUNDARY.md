# Initialized pinned E1M1 boundary

## Active scope

The user accepts **corresponding initialized DOS/Lean E1M1/HMP states** as the
starting boundary. Launch, DOS/filesystem and VGA initialization verification
are no longer on the critical path. Existing loader/read/heap proofs and their
verified evidence remain untouched, historical optional foundations.

This checkpoint is a real captured-data vertical slice, **not complete aiming,
initial-state observational equivalence, or gameplay preservation**.

## Exact synchronization point and provenance

- Unmodified pinned shareware EXE:
  `b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
- WAD: `1d7d43be501e67d927e415e0b8f3e29c3bf33075e859721816f652a526cac771`.
- Existing `e1m1-proof-profile.json`: E1M1, Hurt Me Plenty, player 1, ordinary
  single player, no respawn/fast/nomonsters. Demo contains one zero command.
- Actual capture: first existing authenticated before-tick hook at
  **code+0x2081a**, before the `P_Ticker` CALL; observed tick/leveltime both zero.
  Pinned DOSBox-X normal core, 486, 32 MiB, timedemo, `-nodraw -nosound`.
  The single command is executed only *after* this snapshot; no later matching
  outcome is used to establish the relation.
- Lean: **`Engine.start lumps true false`**, before `advance` or `afterPresent`.
  This runs `Map.load`, `Assets.load`, `Simulation.spawn`, and `DosHeap.startup`.
  The probe uses `state.game.player.syncScene state.game.map`, the exact
  production `Combat.combatScene` expression, not an invented collision Context.
- Observed RNG: play=144, misc=0. Do not identify this with post-wipe state.
  `Engine.afterPresent` changes misc RNG after the first presentation; no
  presentation or wipe correspondence is claimed by this capture.

`capture_initialized_e1m1.py` reuses the existing pinned archive, original EXE
validation, observer, relocation bindings, demo encoder and capture runner.
It builds an isolated additional emulator; no old observer or cache is edited.
The new hook copies host RAM/VRAM backing storage, without guest writes or VGA
aperture reads. It also records registers, EIP, EFLAGS, code/data/segment bases.
The old observer independently emits its established trace fields.

Evidence lives in `artifacts/initialized-e1m1/`:

- `capture/ram.bin`: 32 MiB host RAM backing, retaining heap and stacks.
- `capture/vram.bin`: 2 MiB VGA backing, retained for later work.
- `capture/initial.json`, `binding.json`, `provenance.json`, `dosbox.conf`,
  demo, EXE/WAD copies and trace: exact boundary, commands, configuration,
  address and source/build/hash bindings.
- `lean-initial.json`: exercised production initialization projection.
- `relation.json`: extracted placements, identity mapping, thinker order,
  BLOCKMAP words, stamps, checked counts and authenticated code ranges.
- `bridge-input.json`: shooter words and all stamps extracted from raw RAM.
- `lean-checked.json`: actual production `engineCheck`, `startCheck` and
  `stampCheck` all return true on that captured input.

These are **not restartable emulator save-states**. Host RAM backing does not
represent device overlays; VRAM is saved separately. Device control registers,
CPU lazy-flag internals, scheduler and emulator internals are not serialized.
The initial relation for future pixels/audio still needs those observations and
state components. Neither raw dump nor Lean projection is silently substituted
for a complete `Engine.State` equality.

## Checked, assumed and proved

### Concrete checks actually exercised

The Python validator compares actual raw DOS bytes with the pinned WAD and
production output, rejecting rather than repairing mismatches:

- All 3461 BLOCKMAP words, offsets, leading-zero visits, ordered IDs and
  sentinels; 828 cells in the 36×23 grid. No sorting or deduplication.
- All 475 line geometries, front/back portal heights and relevant line flags.
- All 92 live spawned mobjs, by full THINGS spawn tuple and occurrence order;
  player identity/backlink, position, angle, radius/height, floor/ceiling,
  solid/shootable/noBlockmap flags, linked-list integrity and spawn thinker order.
  All 828 blocklink heads and ordered actor lists match production IDs.
- RNG and initial player/weapon/enemy fields independently agree with the
  established trace observer. Epoch is 1; all 475 line stamps are zero.
- Boundary signature and relocated captured code ranges
  `0x2081a..0x20830`, `0x24150..0x24190`, `0x2b000..0x33500` match the pinned
  original image. This authenticates bytes, not execution of every instruction.

### Explicit empirical/trusted boundary

DOSBox execution, hook timing, host dump extraction, WAD/JSON decoding,
field-offset interpretation, local compiler/build bookkeeping, SHA256 and
production executable evaluation are outside the Lean kernel proof.
The checker's accepted concrete `Engine.start` result is empirical evaluation,
not an in-kernel reduction of the complete WAD/assets initializer.

The generated stamp certificate is kernel checked. Its memory decoding premise
states that the supplied memory's stamp words equal the captured array. It is
not an axiom and does not contain freshness, aim success or future execution.
Python discharges the corresponding equality against raw captured bytes.

The actual dump has relocated **physical addresses**. Existing machine proofs
usually use canonical code/data-object offsets. No blanket subtraction of the
data base has been performed on scalar words. A justified pointer/address
translation and its execution compatibility remain open before applying the
whole original-machine controller theorem to this captured machine.

### Kernel-proved bridge

`Doom/Proofs/InitializedE1M1.lean` proves:

- `supported_of_check`: finite shape data imply the existing
  `E1M1QuerySource.supported` predicate.
- `engine_inputs`: the checker on the actual `Engine.State` aiming projection
  yields the live shooter at index zero, supported query profile, and the four
  original shooter-memory input equalities (x/y/z/height) used by
  `E1M1AimGeometry.Inputs`.
- `started_inputs`: checking the production initializer yields its actual
  successful `Engine.start` state and those input facts. Successful production
  initialization is derived, not supplied separately.
- `fresh_pair`: bounded decoded stamps derive the two existing
  `E1M1AimStampImage.Fresh` premises for epoch+1 and epoch+2.
- Generated `Captured.lean` checks the actual captured array and specializes
  that result to the captured epoch. It assumes only the stated memory decoding
  relation, not the freshness conclusions.

No theorem takes the full `E1M1AimOriginalInputs.execution` hypotheses under a
new name. No new axiom, sorry, native_decide or bv_decide is used. Six bridge and
certificate declarations pass separate transitive strict audits with the
allowlist `propext`, `Quot.sound`, `Classical.choice`.

## Validation and preservation

- 10 focused integration/test methods pass, including actual DOS capture,
  production initialization, raw relation checks, kernel checks and negative
  mutations of code bytes, shape, geometry, pointers, flags, ordering, RNG,
  stamps, provenance boundary, and strict audit output.
- A changed captured stamp makes the generated Lean certificate fail. Changed
  shooter height and future stamp values make the actual production checker
  reject. RED/GREEN logs are retained for each implementation slice.
- 50 connected predecessor tests pass: original demo observer/trace, aiming
  stamp restart/query, and pinned path-map suites.
- Full original proof-target command plus the new bridge: 776 jobs pass.
  Pre-existing warnings were replayed; no new bridge warnings.
- Rebuilt `doom-tests`: 98 core checks pass. The entire Python/game integration
  suite was **not** run.
- Preturn hash baseline covers 789 old Doom source files plus handoff/plan.
  All old Doom sources remain unchanged. Only the intentional docs changes
  differ within that baseline. Existing dirty work is preserved; no reset,
  clean, stash, discard or commit.

Final source/evidence bindings and baseline verification are in
`validation.json`. Raw data remains available rather than discarded after
projecting aiming.

## Next connected obligations (active, not launch/startup)

1. Formalize the physical-to-canonical address/pointer relation needed by the
   existing original-machine semantics; retain raw bytes and prove or explicitly
   bound relocation/extraction assumptions.
2. Turn checked map/actor/list data into the existing `WordImage`, scene-line,
   object/list and portal payload predicates. Derive placement/read/write guards
   from the captured layout, not assumed post-call memory.
3. Derive ray arithmetic, trig-table inputs and candidate-capacity bounds from
   actual queries. Do not assume successful queries or successful division.
4. Connect the initialized boundary to the first actual BulletSlope entry along
   admitted gameplay and prove preservation of the established predicates.
   Current stamp freshness is **not** freshness after arbitrary gameplay.
5. Then use the existing conditional aiming/controller theorem and extend
   preservation over admitted gameplay. Full pixel/audio/full-game parity remain
   separate; none follows from finite capture agreement.

## Reproduction

Use the repository's Python 3.14 environment for archive extraction; system
Python 3.9 lacks `tarfile.extractall(filter=...)`.

```sh
export TMPDIR=/Users/alaska/.hermes/cache/scratch
./scripts/lake build initialized-e1m1-probe Doom.Proofs.InitializedE1M1
.tools/x86-check/bin/python scripts/capture_initialized_e1m1.py
.lake/build/bin/initialized-e1m1-probe artifacts/doom-shareware-1.9/doom1.wad > artifacts/initialized-e1m1/lean-initial.json
PYTHONPATH=scripts:tests .tools/x86-check/bin/python -m unittest test_initialized_e1m1 -v
.tools/x86-check/bin/python scripts/verify_initialized_e1m1.py --kernel
./scripts/lake env lean artifacts/initialized-e1m1/Captured.lean > artifacts/initialized-e1m1/kernel-independent.log
PYTHONPATH=scripts .tools/x86-check/bin/python -c 'from pathlib import Path; from verify_initialized_e1m1 import audit; print(audit(Path("artifacts/initialized-e1m1/kernel-independent.log").read_text()))'
```

The existing DOS capture dependencies were available and the isolated build ran;
there is no unresolved capture blocker for this boundary. The relation and
preservation obligations listed above are real open proof work, not tooling
failures.
