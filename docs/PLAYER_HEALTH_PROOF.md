# Original player damage bookkeeping

`Doom/Proofs/OriginalPlayerHealth.lean` proves the original DOS instructions at
`0x2a616`–`0x2a650` and joins them to the actual ordinary-floor damage CALL,
prologue, entry guards and armor block. Accepted runs now reach `0x2a650`;
rejected runs stop at `0x2a747`, before the epilogue. The continuous bound is
73 instructions, with no reconstructed machine state at the seams.

The new block establishes:

- `player.health = max 0 (oldPlayerHealth - remainingDamage)`.
- `player.attacker` receives the saved source pointer, including at zero damage.
- `player.damagecount = min 100 (oldDamageCount + remainingDamage)`.
- The complete memory effect and preservation of the player, target, stack and
  remaining-damage registers needed by the continuation.

Subtraction and addition wrap at 32 bits **before** the signed comparisons.
The damage counter has no lower clamp. The theorem covers all signed 32-bit
values, including overflowing arithmetic, independently varying player/object
health, and negative counters. It does not assume normal gameplay ranges.

## Proof and composition

`execution` evaluates the proposed instruction listing; `decoded` binds every
instruction to the original bytes. `original_execution` proves the resulting
byte-decoded run and full memory result. It has no memory-separation premise:
source is read after the health stores, so aliasing is retained in its semantics.
`values`, `health_frame` and `memory_frame` expose field results and preservation.
`live_values` connects the separated fields to the shared `PlayerDamage.bookkeep`
helper, which is called by the actual live `PlayerDamage.finish`/`apply` path.

`joined_execution` composes that block with `PlayerDamageEntry.execution_detailed`.
Its initial `Inputs` extend the existing call-boundary relation with the initial
player-health and damage-count encodings and their separation from stack writes.
The proof transports both fields through the prologue and armor, derives the
saved null source and its separation from player health, and preserves armor
through the bookkeeping writes. Same-object field separation holds for
unaligned and wrapping addresses. The combined memory frame permits only the
six existing stack words, two armor words, and three new player fields to change.

`live_correspondence` relates remaining damage, armor/type, player health and
damage count to the actual `PlayerDamage.apply` result. The last observed word
is the **DOS null attacker pointer** for environmental damage. It is not a
proof of the runtime's separate `Combat` source-ID/attacker-index mapping.
The standalone block models arbitrary source pointers; the joined domain has
null source and inflictor, ordinary sectors other than 11, a non-null player
pointer and no skull-flight flag. The initial contracts remain explicit.

## Validation

```sh
./scripts/verify-original-player-health
# With Unicorn installed and local JIT access:
python3 scripts/verify_original_player_health.py --cross-check
python3 -m unittest discover -s tests -p test_original_player_health.py -v
```

The verifier checks the pinned shareware DOOM.EXE hash, exact bytes, LE file
mapping and relocations. The generated theorem uses the extracted byte lists
in the continuous run itself. Its strict audit checks **22 declarations** and
accepts only `propext`, `Classical.choice` and `Quot.sound`; `sorryAx` and native
evaluator axioms are rejected.

Independent Unicorn execution passed **11,808 comparisons** against compiled
`PlayerDamage.apply`: **2,180 accepted and 9,628 rejected**. Checks include
all three CALL sites, two data relocations, four alignments, wrapping object
addresses, protection/skill boundaries, arithmetic extrema, and an existing
attacker value that must be overwritten on acceptance. The checker compares
field values, registers, exits, the exact ordered writes and full dynamic memory.

Five focused tests exercise strict audits, mutated health/attacker/counter/CALL
bytes, missing contracts and incorrect live skill, the edge-case corpus, and
**6,912 continuous native Lean machine paths**. Additional native checks cover
16 arbitrary-source/damage pairs and intentional source/health aliasing: the
attacker receives the new health word, demonstrating why separation is needed.
Existing entry, floor-runtime and full C-versus-Lean damage regressions pass.
These finite comparisons support the model boundary; the theorem itself is
universal over its stated inputs.

## Remaining boundary

This component stops before the tactile branch/call and the separate
`mobj.health` write. The [actor-health continuation](ACTOR_HEALTH_PROOF.md) now
composes both, under the disabled-tactile-device contract, and proves the
signed death/survival choice. The [pain-decision proof](PLAYER_PAIN_PROOF.md)
continues through the RNG CALL/RET and pain choice. State entry, death actions
and handler return remain open. Player health and actor health remain distinct fields.
The extra damage-handler contracts have not yet been transported from the
beginning of the earlier preparation/floor proof. Non-environmental damage,
whole-tic reachability and all-input E1M1 pixel equivalence remain open.

The x86 interpreter is a flat byte-memory model with a separate immutable code
image. Extraction, loader/relocation correctness, interpreter adequacy, and
Lean compilation/runtime remain part of the trust boundary. The repository-wide
test command still has the documented legacy `OriginalDiv`/`OriginalRandom` API
incompatibility; no full-suite pass is claimed.
