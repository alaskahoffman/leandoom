# Tactile call, actor health and death branch

`Doom/Proofs/OriginalActorHealth.lean` continues the original DOS damage handler
from `0x2a650` through `I_Tactile` (when applicable), the actor-health write, and
the signed death/survival branch. The continuous proof starts at the
three ordinary-floor damage CALLs and composes entry, armor and player
bookkeeping without resetting machine state. Its instruction bound is 108.

Player health and actor health are distinct. The previous block clamps
`player.health` to zero. This block writes wrapping `oldActorHealth - damage`
to `mobj.health` **without clamping** and chooses the death continuation when
that signed result is at most zero. Thus overkill and arithmetic overflow are
part of the claim, rather than excluded by a normal-health-range assumption.

The original tactile routine is not an unconditional stub. The proof explicitly
requires its device-enable word at data offset `0x2923c` to be zero. For the
console player, it executes the real argument setup, CALL, three register
pushes, enable check, three pops and RET. For another player it follows the
original skip branch. Enabled-device DOS/hardware calls remain outside scope.

## State and memory contracts

`Inputs` describes the isolated tactile/actor component, including separation
of the enable word from the four new stack writes. `JoinedInputs` extends the
previous initial floor-CALL contract. It requires the actor-health and enable
reads to survive earlier writes, and the actor/player fields and enable word
to be separated from the new stack slots. Player fields must also be separated
from the actor-health write. These are initial-state premises, not assumed
relationships at intermediate states.

The new call writes `SP-32`, `SP-36`, `SP-40`, and `SP-44`, where SP is measured
at the initial floor CALL. The stack returns to `SP-28` before updating actor
health. The memory frame includes those possible writes and the actor-health
word as well as the previously established writes. Unaligned and wrapping
stack arithmetic is retained by the byte-memory model.

The proof is divided into damage capping, console-player lookup, call selection,
callee execution and actor-health blocks to keep kernel checking manageable.
Those smaller runs compose into the continuous byte-decoded run.

## Validation

```sh
./scripts/verify-original-actor-health
# With Unicorn installed and local JIT access:
python3 scripts/verify_original_actor_health.py --cross-check
python3 -m unittest discover -s tests -p test_original_actor_health.py -v
```

The extraction certificate binds exact pinned executable bytes, file offsets
and LE relocations to the theorem. The strict audit passes **31 declarations**,
allowing only `propext`, `Classical.choice` and `Quot.sound`; it rejects placeholder
and native evaluator axioms. The independent checker compares compiled `PlayerDamage.apply`
against the original instructions, including exact ordered memory writes,
registers, exits and dynamic memory. Native Lean fixtures cover both console
and other-player paths, signed health extremes, and intentional violations of
the disabled-device and stack-separation premises.

The original-byte comparison passed **11,808 runs**: **2,180 accepted** and
**9,628 rejected**, with **972 actual tactile CALL/RET paths** and **1,468 death
branches**. It covers all three floor CALL sites, two relocated data layouts,
four alignments, wrapping object pointers, signed extremes and protection/skill
boundaries. Results come from compiled live `PlayerDamage.apply`.

The five focused tests pass, including **6,912 continuous native Lean paths**,
36 isolated signed-health cases, eight byte mutations, weakened input contracts,
and both invalid-device fixtures. The five player-bookkeeping tests, five
entry/armor tests and full C-versus-Lean player-damage regression also pass
(**16 tests total**). These finite checks support the interpreter boundary;
the Lean theorem quantifies over every state satisfying its stated contract.
The full repository suite still has the documented legacy `OriginalDiv`/
`OriginalRandom` API incompatibility; no full-suite pass is claimed.

## Remaining boundary

Accepted runs stop at `0x2a6a6` (death continuation, before source/target argument
setup and `P_KillMobj`) or `0x2a6b6` (survival continuation, before pain RNG).
Rejected runs stop at the earlier `0x2a747` epilogue boundary. This proves the
choice of continuation, not the pain/death actions or handler return. The
[pain-decision continuation](PLAYER_PAIN_PROOF.md) now composes the surviving
path through the actual RNG CALL/RET and pain choice; state/action execution
remains beyond its boundary.

The live observation includes the previous player-health/armor/counter result,
the actor-health word, and the live `killed` flag. The DOS attacker remains the
null environmental source; the runtime's separate Combat identity mapping is
not proved. Earlier-tic reachability, enabled tactile hardware, non-environmental
damage and all-input graphical/game equivalence remain open. The flat x86 model,
loader/extraction and Lean compiler/runtime retain the existing trust boundary.
