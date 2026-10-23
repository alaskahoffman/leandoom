# First pain-state stores and return

`Doom/Proofs/OriginalPainSetter.lean` extends the continuous original-DOS damage
proof through the body and RET of `P_SetMobjState` for the first player pain
state. The theorem begins at any of the three ordinary-floor damage CALLs;
intermediate registers, memory and flags flow through the existing damage,
RNG and pain-handoff proofs into the setter.

Under the explicit initial-state relation, a selected pain response now provably:

- writes state pointer `0x16b38` (state 156), four tics, sprite 28 and frame 6;
- takes the null-action and nonzero-tic branches;
- restores EBX and ESI, returns EAX = 1 and EDX = 157;
- executes RET through the saved address to damage continuation `0x2a6df`;
- preserves the earlier health, armor, damage count, attacker, RNG and hit-flag results.

The joined run uses at most 152 modeled instructions: the earlier bound of 128
plus the setter's 24 instructions. ESP is back at the initial damage CALL's
`SP-28`; this is still inside the damage handler. Rejected, lethal and surviving
no-pain branches retain their earlier boundaries and leave animation fields
unchanged. The whole-memory frame limits writes to the accumulated footprint.

## Link to the running engine

The live relation uses `PlayerDamage.apply`'s actual pain result. State identity
and duration come from the existing `PlayerAnim.enter 156`, which is also used
by `Combat.hurtPlayer`. Sprite 28 and frame 6 are the presentation fields in the
pinned original state table. Lean's `PlayerAnim.State` represents a state index
and tic count, rather than keeping separate sprite/frame fields, so this theorem
does not by itself prove how the renderer displays those fields.

The extracted 28-byte state-table row is `(28, 6, 4, 0, 157, 0, 0)`. Its action
pointer is null: the later state 157 requests the pain sound. This proof covers
entry to state 156, not that later transition or sound.

## Composition and assumptions

The setter reuses the existing decoded instruction listing from the walking
animation proof. Its prologue, body and epilogue proofs specialize that path to
state 156, its original table row and this caller's return address. No x86
interpreter changes are needed.

`JoinedInputs` extends the preceding damage-call relation with the original
pain table and byte-level separation of its reads, animation fields, saved stack
slots and retained results. These are premises about the initial CALL state.
The relation at setter entry is derived from the preceding execution and memory
frame; an intermediate setter result is not assumed. Addresses and arithmetic
use 32-bit words, and separation covers unaligned and wrapping addresses.

The extraction certificate checks the pinned executable hash, code bytes,
loader relocations, RNG table and the pain-state data row's LE page mapping.
The row must have no overlapping relocations. It connects the extracted code
to the continuous live-correspondence theorem. The strict audit allows only
`propext`, `Classical.choice` and `Quot.sound` across 31 declarations.

## Validation

```sh
./scripts/verify-original-pain-setter
# With Unicorn and local JIT access:
python3 scripts/verify_original_pain_setter.py --cross-check
python3 -m unittest discover -s tests -p test_original_pain_setter.py -v
```

The independent original-byte/live-damage comparison passes 12,576 cases,
including 964 pain setter CALL/RET executions. It covers all RNG indices on
survival, death and rejection, all three floor calls, two data relocations, four
alignments and wrapping object pointers. Checks include exact ordered writes,
complete dynamic memory, randomly initialized animation fields, restored EBX,
stack position, next-state register, return address and retained damage results.
Damage/RNG expectations come from the compiled live Lean function; the new DOS
sprite/frame stores are checked against the extracted table.

Native Lean fixtures exercise 9,216 continuous paths and isolated setter
returns. Mutation tests reject changed setter instructions and state-table
fields. Contract tests reject missing setter premises, invalid call sites and
changed skill selection. Non-null actions, zero-tic chaining and incorrect
saved return addresses cannot count as a successful certified setter path.
All five focused tests, six preceding handoff tests and eight existing animation
tests pass (19 total).

## Remaining boundary

This is a conditional theorem for ordinary environmental damage to the player,
with the existing metadata and disabled-tactile premises. Transporting these
premises from full-tic initialization remains open, as do lethal handling,
non-environmental damage, the rest of the damage handler, later pain actions,
rendering correspondence and whole-game equivalence. The [surviving-damage continuation](DAMAGE_RETURN_PROOF.md) now covers
reaction/target bookkeeping after `0x2a6df` and the handler's own return, under
its additional initial layout premises and accepted-survival condition.

The flat x86 semantics, executable extraction/loader and Lean compiler/runtime
retain the project's existing trust boundary. The separate legacy
`OriginalDiv`/`OriginalRandom` API mismatch prevents claiming a full repository
test-suite pass.
