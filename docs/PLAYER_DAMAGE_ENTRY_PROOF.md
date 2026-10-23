# Floor damage entry through armor

`Doom/Proofs/OriginalPlayerDamageEntry.lean` composes a continuous run of the
original DOS executable from any of the three ordinary-floor damage CALLs:
`0x2fb76`, `0x2fba0`, or `0x2fbd2`. It executes the actual CALL, eight-instruction
`P_DamageMobj` prologue, entry/protection guards, and the previously proved armor
block. The bound is 59 instructions. No machine state is reconstructed or reset
at the seams.

The supported domain is ordinary sectors other than 11, a player object with a
non-null player pointer, no `MF_SKULLFLY`, and null source/inflictor pointers.
Damage, health, armor and armor type are arbitrary signed 32-bit values. Both
baby-skill and other-skill branches are covered. Flags, pointers, initial byte
memory and the stack address are otherwise arbitrary subject to the explicit
initial field encodings and stack-separation contract.

The proof covers:

- Return-address and saved-register pushes, local allocation, and source stores.
- Rejecting non-shootable or already-dead players before damage processing.
- Baby-skill arithmetic right shift, including odd and negative values.
- The null-inflictor branch skipping knockback and its possible RNG draw.
- Ordinary-sector dispatch past the sector-11 rule.
- God mode and invulnerability checks, including their signed damage threshold:
  damage at least 1,000 bypasses protection, after skill reduction.
- Both armor arithmetic paths and depletion, using the existing armor proof.

Accepted runs stop at `0x2a616`, before original player-health bookkeeping.
Rejected runs stop at `0x2a747`, before the original epilogue. The stack remains
28 bytes below its call-boundary value. Neither stop means the handler has
returned.

## Statements and live connection

`Inputs` describes the **initial call-boundary memory**, not a hypothetical
post-prologue state. `saved_frame` and `transport` derive all guard and armor
reads through the real writes, including pointer chains and byte/halfword
reads. `execution` supplies a successful decoded-byte run, result, exact exit,
preserved target pointer, stack position, and a whole-memory frame. Only the
six stack words and two armor words may change.

`live_entry` proves the corresponding branch behavior of the actual
`PlayerDamage.apply`: ordinary environmental damage either leaves the player
and RNG unchanged or enters its shared `finish` continuation with skill-adjusted
damage. `live_correspondence` relates the DOS run to that live function's
accepted/rejected result and armor output. It recovers remaining damage from the
live health difference using wrapping subtraction. This observation is not a
proof of the original DOS health-writing, pain or death instructions.

The live refactor extracts the existing armor/health/pain tail into
`PlayerDamage.finish`; `apply` calls that continuation after the same original
checks. The existing full C-versus-Lean player-damage regression still passes.

`floor_handoff` also proves every nonzero request from the preceding floor
component reaches one of these exact sites with the expected target and null
source/inflictor arguments. The additional damage-entry field encodings and
separation premises still need to be transported from the earlier continuous
preparation/floor proof's initial state. We have not claimed a new uninterrupted
proof from the beginning of the game tic.

## Validation

```sh
./scripts/verify-original-player-damage-entry
# With capstone/unicorn installed; Unicorn requires JIT access.
python3 scripts/verify_original_player_damage_entry.py --cross-check
python3 -m unittest discover -s tests -p test_original_player_damage_entry.py -v
```

The extraction tool checks the pinned executable hash, original bytes, LE file
mapping and relocation identities. Its generated certificate binds those bytes
directly to `live_correspondence`. The strict audit passes all 19 declarations
using only `propext`, `Classical.choice`, and `Quot.sound`; placeholder and native
evaluator axioms are rejected.

The independent Unicorn comparison passed **11,296 continuous runs** against
compiled `PlayerDamage.apply`: **1,668 accepted and 9,628 rejected**. It uses all
three CALL sites, two relocated data layouts, four alignments, a wrapping object
pointer, signed extrema, noncanonical nonzero skill/power words, and both sides
of the 1,000/2,000 protection/skill boundaries. It checks the exit, target and
player pointers, stack position, remaining damage, armor fields, full dynamic
memory, and exact stack/armor write sequence. The comparisons support the
interpreter/model boundary; they do not replace the universal proof.

Five focused Python tests cover the axiom audit, mutated CALL/prologue/guard
bytes, required initial relation/site/skill bindings, corpus boundaries, and
6,912 concrete Lean machine paths. Additional native checks cover near-JLE
decoding, truncation rejection, and an intentionally overlapping stack/armor
layout that demonstrates why the separation premise is required.

## Remaining work

The [player bookkeeping proof](PLAYER_HEALTH_PROOF.md) now continues this run
through player health, attacker and damage-count writes. `execution_detailed`
also exports the accepted player pointer and a memory frame relative to the
post-prologue stores, enabling that connection without new seam assumptions.
The [actor-health continuation](ACTOR_HEALTH_PROOF.md) adds the actual
disabled-device tactile CALL/RET, actor-health store and death/survival branch.
The [pain-decision proof](PLAYER_PAIN_PROOF.md) continues through the RNG
CALL/RET and pain choice. State entry, death actions and epilogues remain open.
The non-environmental knockback path, skull-flying objects and sector-11 rules
are separate domains. Earlier-tic reachability and all-input E1M1 equivalence
remain open. The repository-wide test command also retains the previously
recorded legacy `OriginalDiv`/`OriginalRandom` API incompatibility; no full-suite
pass is claimed.
