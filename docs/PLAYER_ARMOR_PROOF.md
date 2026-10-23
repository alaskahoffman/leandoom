# Original player armor absorption

`Doom/Proofs/OriginalPlayerArmor.lean` proves the original shareware DOOM 1.9
armor block agrees with `PlayerDamage.absorbArmor`, the helper called by the
live `PlayerDamage.apply` routine. The block runs from code offset `0x2a5d5`
to `0x2a616`, after the protection checks and before player-health bookkeeping.

The correspondence theorem quantifies over **all signed 32-bit damage, armor
points, and armor-type values**, all initial flags, and every byte memory that
encodes those three inputs. It requires no normal-play range restriction.
It covers:

- No armor: leave damage, armor points and type unchanged.
- Green armor: signed division by three, truncated toward zero.
- Other nonzero armor types: the original sign-corrected arithmetic shift for
  signed division by two, also truncated toward zero.
- Cap absorption at available armor. Clear the armor type when the quotient
  equals or exceeds the available armor, including equality.
- Subtract the absorbed damage with the original 32-bit wrapping semantics.

`execution` proves a bounded run of the proposed instruction listing.
`decoded` checks every listed instruction against the extracted byte decoder;
`original_execution` transfers the result to the actual byte program.
It specifies remaining damage, the complete final byte memory, preserved
ESP/EBP/ESI, and the exit PC. `memory_frame` preserves every word disjoint from
the two possible armor writes, including wrapping or unaligned addresses.
`live_values` and `correspondence` connect this result to the live helper.
`live_inline` proves the extracted helper equals the armor code previously
inline in the live routine.

The limited x86 interpreter now handles register-form IDIV and short JL.
IDIV uses the signed 64-bit EDX:EAX dividend, truncates quotient and remainder
toward zero, rejects zero divisors and quotients outside the signed 32-bit
range, and invalidates undefined flags. The proof establishes that the
original sign-extension sequence produces the right dividend and that dividing
any signed 32-bit damage by three cannot fault. These are proofs in the
existing limited x86 model, not a verification of that model against physical
hardware or of the DOS loader.

## Reproduction and validation

```sh
./scripts/verify-original-player-armor
# Requires the local capstone/unicorn Python environment; Unicorn needs JIT access.
python3 scripts/verify_original_player_armor.py --cross-check
python3 -m unittest discover -s tests -p test_original_player_armor.py -v
```

The extraction tool checks the pinned archive/executable hashes, LE file mapping,
exact bytes and relocation set using the existing original-executable tooling.
The executable SHA-256 is
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
The generated certificate binds the extracted bytes directly to the live-helper
correspondence theorem. Its strict audit checks 11 declarations and accepts only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, native evaluator,
or solver-result axiom is accepted.

The independent comparison passed **12,728 cases** against the compiled Lean
helper. It exercises signed extrema, all armor branches, exact quotient/depletion
boundaries and adjacent values, random 32-bit inputs, four alignments, and a
player address whose fields wrap across the 32-bit address boundary. It checks
remaining damage, armor/type, preserved registers, the entire mapped data memory,
and the exact sequence of writes. These comparisons validate the semantics and
implementation; the universal claim comes from the kernel-checked theorem.

Five focused Python tests cover the certificate, strict axiom rejection,
mutated original divisor bytes, missing input relations and 21 concrete Lean
machine/decoder checks (including IDIV faults and preserved IMUL decoding).
The existing full player-damage C comparison and all five floor-runtime proof
tests also pass after extracting the helper. The repository-wide test command
still has the separately documented legacy `OriginalDiv`/`OriginalRandom` API
incompatibility; no full-suite pass is claimed here.

## Remaining composition

The [damage-entry component](PLAYER_DAMAGE_ENTRY_PROOF.md) now connects this
block to the actual ordinary-floor CALL sites, prologue, shootability/health,
skill and null-inflictor branches, and protection checks. It proves a continuous
59-instruction-bounded run from the CALL boundary to armor completion or the
rejection epilogue, with initial memory/separation contracts.

Those additional contracts still need to be transported from the initial state
of the [continuous preparation/floor decision proof](PLAYER_FLOOR_DAMAGE_PROOF.md).
The [player bookkeeping proof](PLAYER_HEALTH_PROOF.md) extends the CALL/armor
run through player health, attacker and damage-count writes. The
[actor-health continuation](ACTOR_HEALTH_PROOF.md) adds disabled-device tactile
CALL/RET, actor-health writes and death/survival selection. The
[pain-decision continuation](PLAYER_PAIN_PROOF.md) adds the RNG CALL/RET and
pain choice. Pain state entry, death actions and handler return remain open. This is not an all-input E1M1 or
whole-game equivalence claim.
