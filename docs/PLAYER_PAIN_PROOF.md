# Player pain decision and gameplay RNG

`Doom/Proofs/OriginalPlayerPain.lean` extends the continuous DOS damage proof
through the surviving actor's `P_Random` CALL/RET and pain decision. From any
initial state satisfying `JoinedInputs`, all three ordinary-floor damage CALLs
agree with the actual Lean `PlayerDamage.apply` on armor, player/actor health,
damage count, death choice, the gameplay RNG index and the pain flag.

The run's instruction bound is 121. It composes the existing 108-instruction
entry/armor/bookkeeping/tactile/actor-health proof with a 13-instruction suffix.
Machine registers, flags and byte memory pass directly between components.
No intermediate state relation or reset is assumed.

## What the new component establishes

- Rejected damage and lethal damage do not draw pain RNG.
- Accepted, surviving damage draws exactly once, even when pain is skipped.
- The gameplay index increments modulo 256, then selects the original table
  byte. In particular, index 255 wraps to zero before the lookup.
- For the player pain chance of 255, rolls below 255 select pain and roll 255
  skips it. The theorem relates that branch to the live `pain` result.
- The actual CALL writes a return address; the callee updates the index and
  returns through shared stack memory. The proof includes those operations.
- A separate decision-block theorem handles every signed 32-bit pain chance
  and both skull-flight flag values. The continuous player theorem retains the
  established non-skull-flying domain.

The memory frame exports all possible writes. The suffix writes the return
slot at initial `SP-32` and the gameplay RNG word at data offset `0x12720`.
After RET, the stack is back at initial `SP-28`. Existing player/actor result
fields are preserved by explicit separation premises.

## Initial-state contract

`JoinedInputs` extends the actor-health contract with the initial gameplay
index, original table byte, and player metadata pain chance. It requires those
reads to survive the earlier writes and separates the suffix writes from the
fields that must remain unchanged. The info pointer is loaded from actor +92;
the chance is read from info +32.

The skull-flight byte at actor +107 is transported using its containing flags
word at +104. This matters: actor health starts immediately at +108. Requiring
an entire four-byte read starting at +107 to be disjoint from the health store
would make the contract impossible. `frame_high_byte` proves the appropriate
byte preservation from the containing word instead.

All pointer arithmetic and stores retain the flat model's 32-bit wrapping and
unaligned semantics. The underlying ordinary-floor contract still requires a
player, null inflictor/source, a non-sector-11 floor and disabled tactile device.
The live theorem does not extend to general monster/combat damage.

## Validation

```sh
./scripts/verify-original-player-pain
# With Unicorn installed and local JIT access:
python3 scripts/verify_original_player_pain.py --cross-check
python3 -m unittest discover -s tests -p test_original_player_pain.py -v
```

The extraction certificate checks the pinned DOOM.EXE hash, code bytes, file
mapping, LE relocations and complete original RNG table. Its strict audit covers
33 declarations and permits only `propext`, `Classical.choice` and `Quot.sound`.
Placeholder and native evaluator axioms are rejected.

The independent Unicorn comparison passed 12,576 cases against compiled live
`PlayerDamage.apply`: 2,692 accepted and 9,884 rejected, including 1,724 lethal
branches, 968 pain RNG calls, 964 pain choices and four surviving no-pain choices.
It checks exact ordered writes, dynamic memory, stack/register values, CALL/RET
visits and branch destinations. Every RNG index is tested on survival, death
and rejection. The corpus also covers two data relocations, four alignments,
wrapping object pointers, signed health/damage edges and skill/protection gates.
The separate presentation RNG word is checked unchanged in these executions;
the formal live observation currently includes the gameplay index only.

The native fixtures exercise 9,216 continuous paths, 4,096 general pain-decision
cases, a corrupted table byte and a return-slot/index alias. They also check the
new separation contracts on the continuous fixtures. Mutation tests reject
changed CALL, comparison, branch, RNG and table bytes; weakened input contracts,
wrong skill and incomplete axiom audits are rejected too. These are finite
validation checks; the correspondence theorem quantifies over all states that
satisfy the initial contract. All five focused tests and the existing full
C-versus-Lean player-damage regression pass (six tests total).

## Remaining boundary

The continuous run stops at:

- `0x2a6c9`: pain selected, before setting `MF_JUSTHIT` or entering its state;
- `0x2a6df`: pain skipped, before reaction-time/retarget handling;
- `0x2a6a6`: death selected, before `P_KillMobj`;
- `0x2a747`: rejected damage, before the handler epilogue.

Pain state entry and sound/action execution, death actions, the remaining
handler and its return are still open. The next direct continuation is the
`MF_JUSTHIT` update and `P_SetMobjState` handoff. Transporting these damage
contracts from the beginning of the earlier preparation/floor proof also
remains necessary. The [pain-state handoff](PAIN_HANDOFF_PROOF.md) now composes
the flag update and CALL through setter entry, proving all flag bits, the
player/state arguments and the saved return address. The setter body and its
return remain outside that continuation.

This is not whole-game or all-input E1M1 pixel equivalence. Extraction/loader
correctness, adequacy of the limited x86 interpreter, and the Lean compiler and
runtime retain the existing trust boundary. The repository-wide test command
also retains the documented legacy `OriginalDiv`/`OriginalRandom` API mismatch;
no full-suite pass is claimed here.
