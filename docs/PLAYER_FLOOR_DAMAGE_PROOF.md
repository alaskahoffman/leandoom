# Original damaging-floor decision correspondence

`Doom.Proofs.FloorRuntime.correspondence` proves that one original DOS byte run,
starting before player preparation, agrees with the actual preparation and
floor-request functions used by the live combat tick. It builds on
`FloorJoined.correspondence`, which relates that run to the underlying helpers. It covers the reaction timer, turning/thrust,
walking-animation entry, view-height calculation, sector lookup, handler CALL
and prologue, floor-contact check, compiler switch, and ordinary damage decision.

The result includes all eleven previously proved preparation fields, the
requested damage, both RNG indices, and stack position. `execution` additionally
proves the damage-call arguments and a memory frame covering both phases. All
encoding and separation premises concern the original incoming state. There is
no assumed successful handoff or reset of machine memory/registers between phases.

This is a universal theorem under those premises for specials 5, 7, 4, and 16,
on or off the floor. It composes the earlier `FloorCaller.correspondence`,
`FloorEntry.correspondence`, and `FloorDamage.correspondence` proofs. It is not
an enumeration of tested game states.

The endpoint is just before `P_DamageMobj`, or the shared no-damage epilogue.
The proof establishes the requested amount and both RNG indices. The companion
`damage_arguments` theorem establishes the player-object target, two null source
arguments, and that the endpoint's decoded CALL targets original `P_DamageMobj`.
It does **not** establish the effects of that call on armor, health, pain, death,
or further random draws.

## What is checked

- The outer lookup obtains the sector special from the EDX player pointer,
  branches on its nonzero value, moves EDX into EAX, and calls the handler. The
  CALL saves its return address and the prologue saves EBX, ECX, EDX, and ESI.
  Initial byte-separation premises protect the required data from these writes.
- The original handler pointer loads select the player's object, subsector and sector,
  then compare object Z with the map sector's floor. Off-floor execution stops
  before the switch or RNG call; only the five outer stack stores have occurred.
- The switch loads only DX, subtracts 4, compares the low 16 bits to 12, masks
  the index, and reads the jump target from code-segment memory. The proof covers
  arbitrary high bits inherited from Z, and index 12 (special 16) at the upper
  bound. Data memory is not substituted for the original code jump table.

- Specials 5 and 7 request 10 and 5 damage respectively, only without a suit
  and on the 32-tic gate. These cases add no memory writes or random draws.
- Specials 4 and 16 request 20 damage on the same clock gate. Without a suit,
  they do not draw randomness. With a suit, they call the original `P_Random`
  and allow damage only when its result is below 5.
- That random draw occurs **before** the clock test, including tics on which
  no damage is requested. Reversing those tests would change future gameplay.
- The actual seven RNG instructions increment and wrap the index, store it,
  read the original byte table, and return through the same byte-addressed
  stack used by the actual CALL. The full original table agrees with Lean's.
- `clock_mask` relates the original low-byte `TEST ...,31` to `time % 32 = 0`,
  for arbitrary natural-number clocks, including values beyond 32 bits.
- `FloorCaller.memory_frame` describes the entire memory effect: five outer
  stack stores, followed only on the suited heavy-floor path by the nested RNG
  return-address store and RNG-index store. `memory_unchanged` proves every byte
  outside these seven potential word stores is untouched. `stack_position`
  proves ESP is the original value minus 20 at the boundary; the outer handler
  has not yet returned.

`FloorCaller.execution` uses a 42-instruction bound: six for outer dispatch,
five for CALL/prologue, up to 13 for floor contact and switch dispatch, then up
to 18 for the selected decision case. The previous 31-instruction entry theorem
remains available. Short paths stop at their specified exit, so the bound adds no artificial instructions or state resets. The partial
instruction listing is checked against the byte decoder at every listed PC.

## Joining player preparation

The full joined entry is `0x333b1`. `FloorJoined.execution` uses a conservative
267-instruction budget: 225 for the already-proved preparation phase and 42 for
the floor caller/decision. Early exits consume fewer instructions; this budget
does not insert operations. The byte programs share absolute original code
addresses, real CALL/RET instructions, and one data memory. The code-memory
bridge preserves preparation's instruction semantics while allowing the later
switch to read its separate code-segment table.

`FloorJoined.Inputs` contains five initial-state obligations:

1. The existing `PlayerHeightJoin.Inputs` preparation contract.
2. The earlier `FloorCaller.Inputs` floor contract, on the incoming state.
3. Separation of required floor input words from preparation's possible writes.
4. Separation of the selected RNG-table read from preparation's possible writes.
5. Separation of all eleven prepared output words from the floor handler's
   possible stack/RNG writes.

`transport` derives the handler contract at the handoff using preparation's
proved memory frame and preserved EDX/ESP. `handler_frame` then proves the
already-established preparation values survive the floor decision. `execution`
composes those frames back to the original memory, so any word separated from
the combined write footprint remains unchanged across both phases.

The height calculation takes the encoded signed-word clock, while the floor
helper takes a natural-number tic count. Both encodings are constrained by the
same incoming clock memory; the floor decision reads its low byte. Fixtures
exercise negative signed clock encodings paired with their unsigned tic counts.
The suit boolean is likewise related to the original nonzero counter.

This preparation phase does not advance the object's position through later
world/thinker physics. Its proved changes are the eleven projected fields:
angle, two momenta, animation state/tics, reaction timer, view height/delta/Z/bob,
and cached grounding.

## Original executable and trust boundary

Run:

```sh
./scripts/verify-original-floor-joined
# The smaller caller/decision certificate remains available:
./scripts/verify-original-floor-damage
# In a Python environment with Unicorn and Capstone:
python3 scripts/verify_original_floor_joined.py --cross-check
```

The verifier checks the existing hash-pinned shareware `DOOM.EXE`, LE mapping,
relocation identities, caller bytes `[0x333d0,0x333e5)`, entry bytes `[0x2fb20,0x2fb57)`, the switch table
`[0x2faec,0x2fb20)`, floor-case bytes `[0x2fb57,0x2fbdc)`, RNG bytes
`[0x24160,0x2417c)`, and the RNG table's data-object mapping. It generates a Lean
certificate binding those extracted bytes to the correspondence theorem and
strictly audits 40 declarations. The accepted axioms are only `propext`,
`Classical.choice`, and `Quot.sound`; native-decide shortcuts and `sorryAx`
are rejected. No additional proof axioms were introduced.

The new joined verifier also extracts the reaction branch, movement function,
walking-state setter, height CALL, and full height routine. Its separate
certificate binds every program component and both tables, and audits 31
joined/runtime declarations, transitively including the existing preparation and
floor proof dependencies and the actual combat callback’s request theorem. The same axiom allowlist applies. Reports and the generated
certificate are written to `artifacts/original-floor-joined/`.

The instruction semantics remain a deliberately limited x86 model with immutable
code, flat 32-bit data addresses, and code-object-relative PCs. Newly supported
encodings are near JGE, register CMP with sign-extended imm8, register XOR,
absolute EAX load, and INC EAX. INC conservatively invalidates flags; the next
AND establishes the flags used later. This is not a proof of the x86 model,
DOS loader, emulator, Lean compiler, or hardware.

## Caller component contract and remaining work

The caller component begins at `0x333d0`, before the outer sector lookup.
`FloorCaller.Inputs` relates the **initial** state to:

- the EDX player pointer and object/subsector/sector pointer chain;
- encoded Z, sector floor height, and sector special;
- suit presence, clock byte, and canonical gameplay/presentation RNG indices;
- the selected byte of the original random table;
- byte separation of the six potential stack words from all required inputs,
  and of the RNG-index write from the player-object pointer.

`establishes_inputs` derives every field of `FloorEntry.Inputs` after the real
CALL and prologue writes, including the nested RNG CALL/RET memory conditions.
There is no premise about an intermediate execution, preinstalled stack values,
or desired output. The earlier `case_inputs` and `floor_relation` then connect
the handler loads to the live fixed-point floor decision.

The contracts are deliberately sufficient, not minimal: even a path that never
calls RNG supplies the selected table byte and its separation conditions. The
separation conditions need not require an aligned stack or prevent address
wraparound. Checked witnesses include SP=2, where the first unaligned PUSH
crosses address zero. A negative fixture rejects a stack that overwrites the
player-object pointer.

Player preparation is joined through `FloorJoined.Inputs` and its proved
transport. The live wrapper connection is now established as described below.
Establishing the initial DOS/Lean relation from earlier tick phases remains
work, as do applying nonzero damage and the original handler return. The
special-11 finale is outside the ordinary-floor theorem. This is not whole-tic,
whole-game, rendering, or executable equivalence.

## Connection to the live simulation

`Simulation.floorDamageRequest` is the exact function consumed by
`Simulation.hurtFromFloor` through `Simulation.applyFloorEffect`. It reads the
sector at the prepared player's position, the map sector floor (not collision
`floorz`), the simulation inventory's current suit counter, `ticks-1`, and the
current RNG. The application step installs the resulting RNG **before** the
health/armor callback, including a draw that requests zero damage.

`FloorRuntime.effect_inline` proves the extracted function has the previous
inline behavior for every simulation state and damage callback, including lookup
errors. `Simulation.hurtFromFloor_request` binds it to the actual combat callback
and its null-source damage call. `combat_no_damage` proves the full resulting
simulation equals the incoming one with only the RNG replaced when the request
is zero. Nonzero health/armor/pain/death handling is deliberately left outside
the correspondence claim.

The runtime correspondence assumes an explicit `Ticcmd`, successful incoming
scene synchronization, a supported non-floating player actor, a valid initial
map-sector lookup for that actor, the ordinary sector kind, and the existing
DOS entry relation. From these incoming facts, `phase_execution` derives:

- successful live `prepareSectorTick` with the same command;
- the synchronized actor position and all eleven prepared fields;
- unchanged map/secret state for these ordinary damaging sectors;
- the second lookup's success and the exact live floor request.

There is no assumed post-preparation position, floor request, or second lookup.
`phase_handoff` proves the RNG and amount delivered to any damage callback;
`output` observes the actual request before that callback and gives `none` for
preparation/lookup failures. The machine observation is read from the final
original-byte state, including both RNG indices.

The runtime phase starts after the interaction tick's initial tick increment
and button processing. `tick_clock` checks that the subsequent `ticks-1` selects
the pre-increment count, including the first tic. The live tick still calls
sector effects before use/weapons, power-counter decrements, and XY/Z movement.
The outer tick gates, earlier button effects, and later phases are not included
in this theorem.

## Independent validation

The caller component’s optional Unicorn comparison executes the extracted DOS code from `0x333d0`,
matching the joined proof boundary, including the outer lookup, actual CALL and
prologue, floor equality, and switch dispatch. It compares against the compiled live helper for 148,896 cases: all 256 gameplay RNG seeds,
all 32 clock residues, four specials, both suit branches, wider clocks, three
floor-contact positions, non-Boolean suit counters, two relocated layouts, and
four address alignments. It checks request amount, all four damage-call
arguments, RNG-call count, all outer and nested stack writes in order, ESP at
the decision boundary, and unchanged presentation RNG. These runs are validation evidence, not the universal proof.

The new joined Unicorn comparison executes continuously from `0x333b1` to the
same damage/skip boundaries. **52,484 cases passed**, including moving and
reaction-blocked players, walking entry, retained grounding that disagrees with
position, varied view state, all four damaging specials, suit/no-suit branches,
all 256 RNG seeds, RNG wrap, off-floor positions, and unsigned clock encodings.
Two data layouts and unaligned player/object/stack addresses are exercised.
The checker compares the entire dynamic memory page, all eleven preparation
outputs, both RNG indices, every damage argument, stack position, original
return-address words, and the ordered handler writes. The expected preparation
and damage results come from compiled Lean helpers. This independent checker
continues to exercise helper composition; the live wrapper connection is
kernel-checked separately and has concrete runtime fixtures.

The level test probe now accepts the full natural-number damage clock while
retaining signed-word limits for its other fields. This permits comparisons
at clock encodings above `Int32.maxValue` without truncating the helper input.

Regression tests also reject mutated outer lookup/branch/CALL/prologue and
floor/clock/threshold/call/RNG/table bytes, missing initial premises, unsupported encodings, and unknown conditional flags.

Focused validation passed 38 Python tests: 28 floor proof tests, five live
floor-damage regressions, and five prior secret-runtime regressions. They cover
both byte-program halves,
mutated tables/CALLs, required initial premises, and concrete uninterrupted Lean
executions. Runtime fixtures deliberately disagree on incoming player versus
actor position, player versus simulation inventory, and collision versus sector
floor. Negative tests reject incorrect clock, RNG, suit, position, floor, or
command connections. Error fixtures verify which player state survives each
failure and that no damage callback is invoked. All 98
native engine checks passed, and the earlier sector/runtime proof target builds.
The existing secret-sector comparison also passed its 52,052 continuous cases
after extending the shared independent checker.
The repository-wide `scripts/test` currently encounters an existing mismatch:
legacy `OriginalDiv`/`OriginalRandom` still use the previous `X86Routine` API.
This change leaves those targets untouched and proves the required RNG path
against the current byte-memory interpreter. A full-suite pass is not claimed.

## Following damage components

The [armor absorption component](PLAYER_ARMOR_PROOF.md) is proved against the
original bytes and linked to the live helper. The subsequent
[damage-entry connection](PLAYER_DAMAGE_ENTRY_PROOF.md) now executes the actual
floor CALL, prologue, normal-player entry guards, protection checks and armor
continuously. `floor_handoff` connects nonzero floor requests to the three proved
CALL sites and their null source/inflictor arguments.

Its additional field-encoding and stack-separation contracts still need to be
transported from this earlier preparation/floor proof's initial state. The
joined floor claim above still stops at the damage-call boundary. The
[player bookkeeping continuation](PLAYER_HEALTH_PROOF.md) separately extends
the damage CALL through player health, attacker and counter writes. The
[actor-health continuation](ACTOR_HEALTH_PROOF.md) adds disabled-device tactile
CALL/RET and the actor-health/death branch. Pain/death actions and return remain open.
