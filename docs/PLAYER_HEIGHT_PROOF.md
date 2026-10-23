# Original player preparation and complete P_CalcHeight correspondence

**Follow-on:** [the continuous secret-sector proof](PLAYER_SECTOR_JOINED_PROOF.md)
now joins preparation through the actual handler return. Preparation and dispatch
PCs use absolute DOS code-object offsets. Standalone height components retain
their explicitly described local coordinate system.

The latest theorem, `PreparedRuntime.correspondence`, relates the original
reaction/movement/height sequence directly to the live `Player.prepareTick`
method. Eleven preparation fields agree under explicit initial-state and scene
premises. `PreparedState.execution` also proves the return PC, restored caller
ESP, and preservation of other memory from the original entry through return.
The component proofs and continuous execution are detailed below.

`Doom.Proofs.PlayerHeight.Function.observation` proves that the complete original
shareware DOOM 1.9 `P_CalcHeight` routine produces the same four view words as the
live `ViewState.calcHeight` function, under an explicit function-entry contract.
The execution starts at the first PUSH and includes the final RET. The generated
certificate binds this theorem to the extracted original executable bytes.

This is a universal conditional proof, not an inference from the recorded runs.
The separate native/emulator comparison continues to test the model and compiled
Lean runtime independently.

## Complete function contract

The theorem covers all branches: no-momentum, cached grounding, live/dead height
recovery, amplitude and height clamps, delta's zero sentinel, and the redundant
early airborne clamp followed by its overwrite. The arithmetic permits every
32-bit input pattern, including signed overflow; no speed or height bounds are
assumed.

`Function.Inputs` states only facts about the initial state:

- EAX points to a player whose object, view, momentum, ceiling and status fields
  encode the supplied Lean inputs. The caller's cached grounding word and global
  level-time word encode the supplied ground/time inputs.
- Sine data satisfies the shared `ThrustTables` initialization relation.
- View writes do not alias the object, global, status or table reads. The six
  stack saves do not overwrite input fields, and view writes do not overwrite
  the saved registers or return address. Separation is byte-aware and permits
  unaligned or wrapping addresses where the required ranges remain disjoint.
- The saved return address is outside this 302-byte routine.

The result proves bit-for-bit equality of view height, recovery delta, view Z and
bob amplitude, restoration of EBX/ECX/EDX/ESI/EDI/EBP, the correct return PC, and
ESP advanced by four bytes to consume the return address. `Function.execution_bytes`
also proves unchanged reads outside the four view fields and six stack-save
slots. A 100-instruction execution budget is proved sufficient. Scratch EAX and
arithmetic flags are not part of the observation.

`OriginalHeightFrame.lean` provides memory-preservation lemmas.
`OriginalHeightControl.lean` proves the guard branches and early airborne clamp.
`OriginalHeightJoined.lean` composes the blocks without resetting memory,
registers, flags or PC at a seam. It derives every later block's preconditions
from the initial context. `OriginalHeightFunction.lean` adds the six PUSHes,
six POPs and RET and discharges their preservation obligations.

## Kernel-checked blocks

`Doom.Proofs.PlayerHeight.amplitude_observation` covers the original instructions
at `0x33036..0x3306f` (exit `0x33070`). With EAX pointing to the player and the
object's two momentum words related to Lean `Fixed` inputs, it proves that the
stored bob amplitude equals the live `ViewState.bobAmplitude` helper. It also
establishes ECX's player pointer and preserves the stack pointer. No alignment,
momentum range or sign assumptions are needed. The block reuses the existing
universal IMUL/SHRD proof for each square, wraps their sum, quarters it using
signed rounding down, then applies the upper cap `0x100000`.

`offset_observation` covers `0x330b2..0x330d9` (exit `0x330da`). It proves that EAX
contains the exact live `ViewState.bobOffset` result and preserves ECX, the stack
pointer and all memory. Its premises relate the bob and level-time words and
require the existing `ThrustTables` initialized-memory relation. It covers every
32-bit bob word and every 32-bit tic word:

- Multiplication by 409 wraps before the 8191 index mask.
- The resulting address selects the same entry of the engine's sine table.
- The sign correction followed by SAR halves the bob **toward zero**, including
  `INT_MIN`. A plain arithmetic shift would be wrong for negative odd values.
- The final IMUL/SHRD pair matches the engine's fixed-point multiplication.

`quarter_word`, `half_word`, `bob_index` and `bob_table_address` expose these
arithmetic facts separately. The amplitude proof includes overflow cases where
the wrapped sum becomes negative; it does not assume bobbing is nonnegative.
Both helpers are called by the actual `ViewState.calcHeight` implementation.
The table contents are a formal precondition; extraction and comparison of all
10,240 entries remain an independent empirical initialization check.

`Doom.Proofs.PlayerHeight.recovery_observation` covers the original instructions
at `0x330e1..0x33136`. With ECX pointing to the player, EBP equal to the live-state
value zero, and the height/delta words related to a Lean `ViewState`, it proves
that the final words equal the live `ViewState.recoverHeight` helper. It also
preserves EAX's bob offset, the player pointer and stack pointer.

There are no numeric range assumptions on height or delta. The claim includes
all 2^64 input pairs, signed tests and wrapping addition. In particular:

- Recovery first adds delta to height.
- The upper clamp resets delta to zero.
- The lower clamp replaces a nonpositive delta with one raw fixed-point unit.
- A nonzero delta then gains `0x4000`; if wrapping makes the result zero,
  the code replaces it with one rather than stopping recovery.

`ceiling_observation` covers `0x33137..0x33156`. The grounded view adds object Z,
view height and bob offset, then clamps to ceiling minus four map units.
The additions/subtraction wrap **before** the signed comparison. This matches
`ViewState.clampZ`, now called by the live `calcHeight` function. The contract
relates the initial object/height/offset fields and requires that writing view Z
does not overwrite the object's ceiling word.

`airborne_observation` covers the final overwrite at `0x330a3..0x330b1`, its
original near jump, and the store at `0x33154`. It proves that the incoming view Z
is irrelevant: the result is object Z plus current view height. A further
`airborne_previous_store` theorem allows an arbitrary prior view-Z store,
provided it leaves the object's Z intact. Thus a prior clamped view-Z value cannot
survive this tail. The composed function proof now includes the earlier
conditional clamp's actual execution as well; its result is not assumed.

Each statement runs the byte decoder, not an assumed high-level replacement.
The complete 302-byte routine's proposed instruction listing is separately
checked against that decoder. Memory remains byte-addressed and accesses can
be unaligned. The new decoder forms fail closed on unsupported encodings; SAR
invalidates flag information except for a zero masked count, and signed branches
require known flags.

## What is still unproved

The caller, dataflow bridge and continuous shared-origin execution are now
proved as described below. The combined public observation covers eleven
preparation fields and restored caller ESP, and connects that projection to
`Player.prepareTick`. A complete player/world-state relation and the remaining
P_PlayerThink actions still need to be connected. The live wrapper assumes
successful scene synchronization, an actor at index zero, and a nonfloating
player. Establishing these premises from reachable states remains open.

The current theorem does not establish whole-game correspondence, reachability,
DOS loading, segmentation, memory faults, physical timing or Lean compilation.
The flat x86 model is the same explicit modeling boundary used by earlier proofs.

## Original bytes and validation

The extractor pins the complete routine at original code offset `0x33030`, file
offset `0x75044`, length 302 bytes, and checks all three data relocations. Original
executable SHA-256:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

```sh
./scripts/verify-original-player-height
python3 -m unittest discover -s tests -p 'test_original_player_height.py'
# Capstone and Unicorn are required; Unicorn's JIT needs execution permission.
python3 scripts/verify_original_player_height.py --cross-check
```

The generated certificate checks the original bytes, all five block observations
and the complete function observation/execution theorem. Its axiom audit allows only `propext`, `Classical.choice` and
`Quot.sound`; omitted audits, proof holes and unchecked native axioms fail.

The independent harness runs the entire original function, including saved
registers and RET, against `ViewState.calcHeight` in the compiled fidelity probe.
Its 50,132 cases cover all 8,192 bobbing phases with both live and non-live states,
explicit height/delta boundaries, signed extrema and deterministic random states.
Cached ground and no-momentum are varied independently. The harness also varies
unrelated cheat-flag bits and nonzero player-state encodings, including `INT_MIN`. Two relocated data bases
and unaligned player/object/stack addresses are used.

Each comparison checks all four view fields, the complete dynamic memory page,
six preserved registers, stack restoration/return and allowed store addresses.
The sine table is independently extracted and compared with the compiled Lean
table; this table initialization check is empirical. The report records branch
coverage, including the overwritten early clamp and zero-delta sentinel.

The earlier standalone-function run passed all 50,132 comparisons, all 13
then-existing height-proof regression tests, and 98 built-in engine checks. The complete proof and its generated
certificate build successfully. The strict axiom audit passed; no proof holes
or unchecked native axioms were introduced.

Mutation tests reject changes to the multiply shifts, quarter shift, cap branch,
tic multiplier, index mask, sign correction, stack saves/restores, guard branches,
early-clamp branch and RET. Negative contract tests reject omitted sine-table,
stack-separation or return-address premises.

This milestone changes proofs and verification tooling only. No live comparison
service was restarted, and these function-level checks do not imply a complete
gameplay replay or whole-game theorem.

## Original height CALL and reaction-to-height dataflow

`OriginalHeightCaller.lean` proves the original five-byte CALL at `0x333cb`
(file offset `0x753df`, bytes `e8 60 fc ff ff`), the complete height routine,
and return to `0x333d0`. It uses the height routine's `0x33030` origin, so the
call/return PCs are `0x39b` and `0x3a0`. Its 101-instruction budget includes the
CALL. Unlike the standalone function contract, no saved return address is
assumed: `entry_return` derives it from the executed instruction. The theorem
restores the caller's original ESP and six saved registers, proves the four
view words, and preserves reads outside view writes and all seven stack stores.

`OriginalPlayerGround.lean` proves grounding after the existing movement/reaction
execution. Movement refreshes the global word from the original height/floor
comparison. A nonzero reaction timer preserves the old cached flag, including
when a timer of one becomes zero and for negative timer encodings. Grounding
uses the timer before decrement. These are initial-state layout contracts,
not assumptions about an intermediate result.

`OriginalPlayerHeightJoin.lean` then proves:

- `reaction_load`: reads disjoint from the complete reaction/movement footprint
  survive either branch.
- `establishes_height`: the reaction result satisfies the full height-call
  contract using updated momenta, the correct grounded flag, and transported
  player/view/table inputs. It requires no intermediate height-entry premise.
- `observation`: executing the reaction region and then the height CALL yields
  the same four view fields as applying the Lean movement/reaction and height
  functions in sequence. The exact memory, registers and flags pass across
  the seam; only the explicit region-local PC convention changes.

This earlier theorem is a **compositional observation with separate code origins**.
It is retained as a component result; the continuous theorem below closes that boundary. The reaction proof now uses
absolute DOS code-object offsets; the standalone height proof uses `0x33030`. Their seam addresses are proved
to denote the same original instruction. The common-origin proof below executes every CALL with its actual shared-origin
return word, rather than rebasing old saved words. Neither result establishes
the complete player tic or whole-game reachability.

The certificate now extracts and checks all five source regions (reaction
caller, movement function, walking-state setter, height CALL, height function),
including all declared data relocations, and audits the new bridge theorems.
Additional mutation tests reject altered call opcodes/targets and altered
upstream code. Negative contract tests reject missing CALL-stack, input-read,
and cached-ground protection.

```sh
# Independent execution starts at the actual CALL; no return word is supplied.
python3 scripts/verify_original_player_height.py --cross-check --caller-context
```

The caller-mode harness checks all 50,132 height cases, the entire dynamic
memory page, seven stack writes, six preserved registers and exact return/ESP.
These are CALL/function comparisons; they do not claim a new emulator comparison
of the entire reaction-plus-height sequence.

The caller/dataflow milestone passed all 17 height-proof regression tests and
the expanded certificate/axiom audit. Caller-mode comparison passed all 50,132
cases. No engine code changed, and the live comparison services were left running.

## Continuous player-preparation execution

`PlayerPreparation.observation` now binds the five extracted original regions
into **one `X86Routine.run`**. It starts at original address `0x333b1`, executes
the reaction decision and either movement/animation or decrement/skip, calls
`P_CalcHeight`, and returns at `0x333d0`. All PCs now use absolute DOS code-object offsets:

| Boundary | Shared PC |
| --- | --- |
| Reaction decision | `0x333b1` |
| Movement function | `0x33160` |
| Movement CALL return | `0x333c9` |
| Nested walking-state CALL return | `0x3325e` |
| Height CALL | `0x333cb` |
| Height function | `0x33030` |
| Height CALL return / final observation | `0x333d0` |

There is no PC rebase, memory reset, or new input assumption at the seam.
All return words are written by the executed CALL instructions in this one
address convention. The height CALL overwrites the previous movement return
slot with `0x333d0`; the proof does not manually patch the saved stack.

`OriginalHeightShared.lean` reuses the existing body proof. The body's partial
listing excludes RET, while `Function.program` supplies the complete listing.
`Shared.execute_shift` checks that each return-free body instruction relocates
without changing data or registers, including every branch target.
`Shared.lift_prefix` transports its execution path. The epilogue's real RET is
then proved separately using its unmodified stack-supplied return word. This
avoids incorrectly treating RET as an ordinary relative branch.

`OriginalPlayerPreparation.lean` embeds both regions into the same decoded-byte
program and composes the reaction prefix with the height call execution. Its
225-instruction bound is the sum of the existing 124 and 101 bounds, not a
conjectured timeout. `execution` proves the final PC, all four view words, caller
ESP, and preservation of reads outside the height/view/stack footprint relative
to the reaction result. The same initial `PlayerHeightJoin.Inputs` contract is
used; no new intermediate-state assumptions are introduced.

The generated `preparation_checked` certificate states the observation directly
against all five extracted byte lists. Its axiom audit also checks the relocation,
CALL-return, shared-height execution and continuous-execution theorems. All
use only the existing allowed axioms; no proof holes or unchecked native axioms.

```sh
./scripts/verify-original-player-height
python3 -m unittest discover -s tests -p 'test_original_player_height.py'
python3 scripts/verify_original_player_height.py --cross-check --preparation-context
```

The independent continuous harness executes all five original regions in one
Unicorn run per case. It compares against compiled Lean movement, animation,
reaction and height functions. Its 52,052 cases combine the height test matrix
with timer/position/cached-ground/animation/command boundary combinations.
Checks include all motion, animation, reaction and view fields, the full dynamic
memory page (including old scratch and nested-call stack contents), cached-ground
word, six preserved registers, caller ESP, actual return-address stores and the
write footprint. Two data relocation bases and unaligned layouts are retained.
The eleven preparation fields now also have formal postconditions below.
The full-page and additional register checks remain independent empirical
coverage; they do not themselves establish universal postconditions.

Next: carry this preparation relation into the remaining player-tick actions,
and ultimately establish the initial contracts from whole-game reachable-state
invariants. Rendering, whole-tic and whole-game equivalence remain outside this
theorem.

Validation for the continuous theorem passed: the kernel build and strict
axiom audit, all 21 height/preparation regression tests, and all 52,052 continuous
original-byte emulator comparisons. Only proof and verification code changed;
the live comparison services were not restarted.


## Eleven-field preparation and the live runtime

`OriginalPreparedState.lean` extends the continuous theorem with these outputs:

| DOS field | Live Lean projection |
| --- | --- |
| Object angle | `body.angle` |
| Object horizontal momentum X/Y | `body.momx`, `body.momy` |
| Object state pointer and state tics | encoded `animation.frame`, `animation.tics` |
| Object reaction timer | `reactionTime` |
| Player view height, delta, Z, bob | `view.height`, `view.delta`, `view.z`, `view.bob` |
| Global grounded word, interpreted as nonzero | `cachedOnGround` |

`retained_safe` derives protection of the seven earlier outputs from the
**existing** `PlayerHeightJoin.Inputs` contract. There is no additional
nonaliasing assumption and no assumed intermediate result. The height call
therefore cannot overwrite movement, animation, timer or grounding results.
`PreparedState.execution` composes the two memory frames: reads disjoint from
the combined write footprint equal their values in the original entry memory.
The certificate's `prepared_state_checked` states the eleven-field observation
and caller stack directly against all five extracted byte lists.

`OriginalPreparedRuntime.lean` projects the same fields from the live `Player`
record. Its `prepare` lemma unfolds the actual `Player.prepareTick` and
`Scene.preparePlayerPhysics` implementations. `correspondence` then equates the
DOS final-memory projection with the live method's result. The certificate's
`runtime_checked` binds this claim directly to extracted executable bytes.
It covers every explicit `Ticcmd` under these premises:

- `p.syncScene m = .ok scene`;
- `scene.things[0]? = some actor`;
- the actor is nonfloating;
- the existing DOS entry contract encodes `actor.motion p.body`, animation,
  command, reaction timer, view, level time and cached grounding, with the live
  player-state flag.

The wrapper records errors as `none`; it never supplies default fields for a
failed preparation. The premises prove successful execution. Explicit commands
bypass keyboard translation. Scene synchronization and collision geometry are
not proved equivalent by assuming synchronization succeeds: the DOS input
relation must still encode the synchronized actor. The helper-level theorem
also covers the non-live height branch, whereas the runtime connection matches
the live branch actually used by this method.

These eleven fields are a preparation projection, **not the entire Player
record**. Position integration, collision, inventory, later actions and the
world-state relation remain separate obligations. No renderer or engine behavior
was changed for this proof.

Validation for the eleven-field/runtime extension passed: **24 regression tests**,
**40 audited declarations**, and **52,052 independent continuous original-byte
comparisons**. The new regressions check distinct offsets for every projected
field, noncanonical true grounding words, rejection of an incorrect value for
each of the eleven outputs, and the live wrapper's required scene premises.
The native/emulator comparison still runs the compiled helper composition;
the connection to `Player.prepareTick` itself is the kernel-checked wrapper
proof, not an additional independent emulator claim.


The following sector decision is now connected in
[the sector dispatch proof](PLAYER_SECTOR_DISPATCH_PROOF.md). It preserves this
preparation projection and the player pointer through both branch outcomes,
using explicit initial read protection. The [joined secret-sector proof](PLAYER_SECTOR_JOINED_PROOF.md)
continues through that handler's CALL and return. Other sector effects and later
actions remain open.
