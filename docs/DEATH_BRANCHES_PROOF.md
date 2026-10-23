# Original death decisions

`./scripts/verify-original-death-branches` checks the original DOS instructions
from `P_KillMobj` at `0x2a38c`, where the proved weapon-drop call returns, through
two decisions used by live `Death.kill`:

- Only the console player's death calls `AM_Stop`, and only if automap is active.
- The extreme death state is selected exactly when signed health is strictly
  below the 32-bit negation of spawn health and the extreme state ID is nonzero.
  Otherwise the normal death state is selected.

The helpers `Death.shouldStopAutomap` and `Death.deathState` were factored out of
existing live code without changing its behavior. The proofs refer to those
helpers, not a separate test-only specification.

## Precise theorem boundary

`DeathBranches.execution` follows both branches with a bound of 26 modeled
instructions. If automap shutdown is needed it stops at the actual `AM_Stop`
entry (`0x24f90`), with return address `0x2a3c8`. Otherwise it follows the death
selector and stops at the actual `P_SetMobjState` entry (`0x30ea0`), with object
in EAX, selected state in EDX, and return address `0x2a3f1`.

It also proves that EBX retains the object pointer, ESP decreases by four,
the return address is written at that stack location, and all disjoint memory
words retain their values. The selector's separate execution theorem describes
all register effects for arbitrary 32-bit health and spawn-health values,
including `-INT32_MIN = INT32_MIN`. Equality at the threshold selects normal
death; an absent extreme state also falls back to normal.

The input relation requires the console index, victim player pointer, automap
word and object metadata to encode the corresponding Lean values. Player slots
range over all four slots. State IDs are observed through 32-bit encoding;
the extreme ID must be below `2^32` so its zero test is preserved. The normal
ID is returned modulo `2^32` (actual Doom state IDs fit this width).

`KillDeathBranches.joined_execution` now composes this segment with the lethal
floor-damage and weapon-drop chain. It starts at any of the three supported
floor damage CALL sites and reaches the same two callee entries with a bound
of 239 modeled instructions. Registers, memory, flags and PC are continuous
across the boundary; there is no reset or assumed intermediate machine state.

The new initial-memory contract supplies the console/automap words and death
metadata, plus separation from earlier writes. The proof derives the object
pointer from the preceding execution, transports those reads through its frame
theorem, and derives health from the **post-damage** observation. It does not
substitute the original health or assume the death-selector contract at the
intermediate boundary. The final CALL preserves the earlier damage fields,
corpse height/flags, kill and frag counters, player dead state, and weapon
state/tics/height. ESP is the original ESP minus 56; the final return address
occupies that stack word.

The earlier bookkeeping and weapon-drop theorems now have detailed variants
that expose the preserved object pointer. Their original interfaces remain
available as wrappers. The joined theorem retains their original scope:
ordinary environmental lethal player damage, disabled tactile hardware, and
fist/pistol/shotgun weapon lowering under the documented encoding and memory
separation premises.

The separate [automap shutdown proof](AUTOMAP_STOP_PROOF.md) now follows this
guard through the ten cache-retagging calls and into the actual DOS notification
branch. Its initial cache contract has not yet been transported from the lethal
floor entry.

`AM_Stop` is not replaced by a flag-clearing stub. Its resource-tag changes and
status-bar notification are outside this theorem. The death state setter and
its callbacks, subsequent random tic adjustment, item drops and final returns
are also outside this theorem. No whole-death or whole-game equivalence claim
follows from this segment alone.

## Binary binding and validation

The verifier checks the pinned shareware executable SHA-256, LE code mapping,
all 101 instruction bytes, and all three data-object relocations. It generates
a Lean certificate that binds the extracted bytes to the universal theorem
and audits 20 declarations. Only `propext`, `Classical.choice` and `Quot.sound`
are accepted; `sorryAx`, native decision axioms, missing declarations and extra
certificate output are rejected.

The model now decodes register `NEG` (`F7 /3`). It deliberately invalidates its
flags; the following original `CMP` supplies the flags used by the selector.
This is not a claim of full x86 NEG flag equivalence. Memory NEG remains
unsupported. Decoder regressions exercise all eight registers, signed
boundaries, preserved registers and rejected encodings.

For independent execution checks, use a Python environment with Capstone and
Unicorn:

```sh
python scripts/verify_original_death_branches.py --cross-check
```

The current corpus executes 54,424 original-byte paths, checking all registers,
ordered writes, return addresses and mapped memory against compiled live
`Death.deathState` and the automap decision. It covers all console/victim slot
pairs, zero and nonzero automap values, exact thresholds and neighboring values,
signed extremes, absent extreme states, random 32-bit metadata, unaligned
objects/stacks and a wrapping stack. These executions validate the machine
model; the universal claim comes from the kernel-checked theorem.

A second execution check continues 1,468 lethal cases from the original floor
CALL through weapon lowering and the new branches. Metadata and weapon setup
occur before the floor CALL. The harness observes the weapon-call boundary and
resumes the same emulator without replacing registers or memory. It checks
compiled live damage, corpse, bookkeeping, weapon-drop and death-state results,
ordered writes and retained memory, including both data bases, all four player
slots, all three floor CALL sites and all three terminal outcomes (automap,
normal death and extreme death).

Eight certificate/decoder/loader/helper tests cover the new segment and join.
Negative certificates reject missing initial contracts or lethality, wrong
entry sites/bounds, use of pre-damage health, altered retained weapon state,
and wrong stack/return results. Existing weapon-drop and kill-bookkeeping
regressions are also checked. The full repository suite was not run.

The DOS loader, emulator and instruction-model fidelity, compiler/runtime, and
initial memory relation remain trust/connection boundaries. The proof observes
abstract machine memory, not physical hardware or a completed rendered frame.
