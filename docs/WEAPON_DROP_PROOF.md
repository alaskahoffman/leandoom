# Original dead-player weapon call chain

`Doom/Proofs/OriginalWeaponDrop.lean` proves the complete original DOS call
chain from `P_DropWeapon` at `0x2d2c0` to its return into `P_KillMobj` at
`0x2a38c`. It follows `P_SetPsprite`, its indirect call through the original
state table, the already-proved dead-player `A_Lower`, and all three returns.
The instruction bound is 55. The dispatcher and setter prefix are factored into
`OriginalWeaponDropDispatch.lean`.

For fists, pistol, and shotgun, every 32-bit fixed-point starting height, and
arbitrary registers/memory satisfying the stated encoding and byte-disjointness
premises, the theorem establishes:

- The selected state is the live engine's `Weapon.down` state (3, 11, or 19),
  represented by the corresponding original state-table pointer.
- The weapon state's tic count is one.
- The final height equals live `Weapon.lowerHeight y true`, including wrapping
  arithmetic, fractional bits, signed comparison, and the bottom clamp.
- Execution returns to `0x2a38c`, with ESP advanced by four. EBX, EDX, ECX, ESI,
  EBP, and EDI are preserved; EAX contains the next state index.
- Only the seven stack words and the psprite's state, tics, and height may change.

The proof derives the callback contract from initial memory through every
preceding write. It does not assume callback results, reset registers at a
join, or replace the indirect action with an oracle.

`X86Routine.callMemory` models near indirect memory CALL, loading its target
before pushing the return address. This matters when the operand uses ESP or
aliases the new return slot. Register-indirect and far CALL forms remain
unsupported. Code pointers use the model's common code origin; interpreting
DOS loader relocations remains an explicit external boundary.

## Continuous lethal-damage composition

`Doom/Proofs/OriginalKillWeaponDrop.lean` joins this callee to the existing
lethal environmental floor-damage path. Starting at any of the three original
floor CALL sites, the bound is 213 instructions through the weapon-drop return.
Earlier damage, corpse height, kill credit, frag, dead-state, and solidity
observations are preserved alongside the new weapon result.

The added premises describe original-memory weapon/table fields and separation
from earlier writes. The proof derives dead state and the saved return address
from the preceding execution. It does not require the player to be dead at the
original floor-call entry.

## Checking

```sh
./scripts/verify-original-weapon-drop
# With Unicorn installed; its JIT may require a less restrictive sandbox:
python3 scripts/verify_original_weapon_drop.py --cross-check
python3 -m unittest discover -s tests -p test_original_weapon_drop.py
```

The executable is pinned by SHA-256. Extraction checks all three code regions,
file offsets, code relocations, the three down-state selectors, and three state
table entries. The callback pointers must have code-object relocations to
`0x2d490`; the selector and state-base operands must reference the data object.
The verifier also reruns the preceding kill-bookkeeping extraction/certificate.
The new generated Lean certificate checks decoded bytes and table contents, then
specializes both the universal callee and continuous lethal-run theorems. Its
19 audited declarations and the preceding certificate's 27 declarations permit only
`propext`, `Classical.choice`, and `Quot.sound`.

The independent emulator comparison runs 67,614 full call chains against
compiled live `Weapon.drop`: every integer half with varied fractional bits,
signed/clamp boundaries, and random words. It checks state/tics/height, all
registers, ordered writes, surrounding memory, unaligned player addresses,
wrapping stacks, and high-address player storage. There are 33,955 below-bottom
and 33,659 clamped cases. Stack and player storage remain disjoint, as required
by the theorem. These comparisons are tests; the theorem quantifies over all
heights under its premises.

Negative certificates cover altered code, table selectors/tics/misc/action/next
fields, missing contracts, wrong results, and wrong return targets. Loader tests
reject missing or incorrect action relocations. A decoder fixture checks
truncation, unsupported CALL forms, overflow rejection, and target-before-push
behavior when the operand aliases the stack write.

Seven new proof, decoder, and relocation tests pass, alongside the 31 existing
weapon-lowering, kill-bookkeeping, weapon, and death tests. The strict audit
rejects missing declarations, additional output, `sorryAx`, and native evaluation
axioms. These are focused checks; the full repository suite was not run.

## Scope

The live correspondence relates selected state IDs and the height helper used
by the live engine. The enclosing partial `Weapon.enter` dispatcher is exercised
by the native comparison; it is not itself unfolded in the theorem. This is a
flat-machine correspondence proof with initial-memory contracts, not a proof
of the loader, full x86 semantics, the Lean compiler, or all possible game
inputs. Automap handling, death-state selection/actions, timing RNG, and the
remaining kill/damage returns are still beyond this boundary.


The subsequent [death-branch segment](DEATH_BRANCHES_PROOF.md) now proves the
original automap decision and normal/extreme state choice from this return
address. `KillDeathBranches.joined_execution` now transports its entry contract
through this lethal-damage theorem and preserves the earlier observations;
the callee effects remain separate obligations.
