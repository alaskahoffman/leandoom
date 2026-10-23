# Rejected damage returns and combined nonlethal correspondence

`Doom.Proofs.OriginalDamageRejected.lean` extends the
[surviving-damage return proof](DAMAGE_RETURN_PROOF.md) to rejected hits. The
combined theorem starts at any of the three original floor-damage CALL sites
and ends immediately after that CALL for every nonlethal result satisfying its
initial-state contract. Both accepted surviving hits and rejected hits are
covered by one theorem; callers no longer need an `applied = true` premise.

Here “nonlethal” means that the actual `PlayerDamage.apply` result has
`killed = false`. This also includes a rejected hit against an already dead
target. It does not assert that every such initial target is alive.

## What is proved

`nonlethal_execution` proves that the original decoded instructions:

- reach `callSite + 5` through the handler's RET;
- restore ESP, EBP, ESI and EDI from the real CALL/prologue saves;
- produce the live result's armor, player and actor health, damage count,
  attacker relation, gameplay RNG index, hit flags, animation and reaction time;
- preserve memory outside the appropriate write footprint.

The footprint depends on the outcome. Accepted surviving hits retain the
previous damage/pain/reaction footprint. Rejected hits write only the six
CALL/prologue stack words. The rejected execution theorem establishes the
stronger equality: final memory is exactly `PlayerDamageEntry.saved s pc`.
It does not claim that the stack remains unchanged.

Rejected hits retain the old attacker pointer; an accepted hit with null source
writes zero there. The new `liveFields` observation accounts for this distinction.
Rejected hits also retain reaction time and consume no random draw. No live
gameplay code needed changing for this step.

## How it composes

The earlier guard proof decides rejection from shootability, health,
invulnerability, god mode and skill-adjusted damage. `rejected_live` connects
this decision to the actual live function, including the damage-1000 protection
bypass and the baby-skill shift before that test.

`rejected_prefix` follows the real CALL, prologue and guard path to `0x2a747`.
The five remaining instructions release 12 bytes, pop EBP/EDI/ESI and return.
The saved return address and register values are derived from the prologue's
stores. Intermediate memory or successful return is not assumed.

The standalone rejected `joined_execution` theorem needs only
`PlayerDamageEntry.Inputs`, plus rejection. It needs no pain-state, RNG-table or
tactile-device metadata. The combined theorem uses the surviving proof's
contract plus byte-level separation of observed fields from stack saves. That
extra separation is necessary: if a saved register aliases the attacker field,
the original really does overwrite that field.

The rejected path has an upper bound of 40 instructions; the combined run uses
the existing 166-instruction bound. These are per-call bounds, not bounds on
input sequences or evidence from enumerating all game states.

## Reproduction and validation

```sh
./scripts/verify-original-damage-rejected
# With Unicorn installed and local JIT access:
python3 scripts/verify_original_damage_rejected.py --cross-check
python3 -m unittest discover -s tests -p test_original_damage_rejected.py -v
```

The verifier reuses the pinned executable and byte manifest from the surviving
return proof. It extracts and checks all 16 code/table units and compiles a
certificate that applies the combined theorem to the extracted instructions.
All 28 audited declarations depend only on the permitted standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The independent emulator comparison passes 12,576 cases: 9,884 rejected returns,
968 accepted surviving returns, and 1,724 cases that stop at the existing lethal
boundary. Thus 10,852 cases execute the full handler RET. The checks compare
exact ordered writes, dynamic memory, registers, return addresses and live Lean
results, including retained attacker, animation, reaction timer and RNG fields.
They cover all three CALL sites, four alignments, two relocated data bases and
wrapping object addresses. This comparison is supporting test evidence; the
universal claim comes from the kernel-checked theorem under its premises.

Native fixtures exercise both outcomes across every RNG index, all three sites
and four alignments; rejected calls with unavailable pain/RNG/device metadata
and wrapping stacks; protection/skill boundaries; and an explicit stack-alias
counterexample. Certificate tests reject changed guard/epilogue bytes, missing
initial contracts, omitted survival premises and a changed skill setting.
All five focused tests and eleven existing damage-entry/return regression tests
pass (16 total).

## Remaining boundary

This closes rejected and accepted surviving **ordinary, null-source floor
damage** calls under the stated initial relations. Accepted lethal damage still
stops at `0x2a6a6` in this theorem. The subsequent
[kill-entry proof](KILL_ENTRY_PROOF.md) follows that branch through the kill CALL
and corpse setup; later kill handling and the lethal return remain open.
Special-sector-11 behavior, non-environmental damage, later pain actions and
transport of the initial relations from the surrounding full player tic remain
separate obligations.

This is not yet a proof of all `P_DamageMobj` paths, rendering, a complete tic or
whole-game equivalence. The flat x86 semantics, external extraction/loader and
Lean compiler/runtime retain the existing trust boundary. The unrelated legacy
`OriginalDiv`/`OriginalRandom` API issue still prevents claiming a full repository
test-suite pass.
