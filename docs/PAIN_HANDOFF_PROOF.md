# Pain flag and state-setter handoff

`Doom/Proofs/OriginalPainHandoff.lean` extends the continuous original-DOS damage
proof through `MF_JUSTHIT` and the actual `P_SetMobjState` CALL. Under explicit
initial-state contracts, all three ordinary-floor damage CALLs agree with the
live Lean damage result on the established health/armor/RNG observations and
whether the first player pain state is requested.

When pain is selected, the original machine now provably:

- changes its complete flags word to `oldFlags | 0x40`, preserving every other bit;
- passes the original player object in EAX and state number 156 in EDX;
- writes return address `0x2a6df` to the stack;
- reaches `P_SetMobjState` at `0x30ea0`, with ESP at initial `SP-32`.

Otherwise, the flags word is unchanged and no state-setter request is emitted.
Rejected, lethal and surviving no-pain paths retain their earlier exit boundaries.
The continuous bound is 128 instructions: the preceding 121-instruction proof
plus seven handoff instructions, with the same registers, flags and memory
throughout.

## Instructions and memory

The original sequence loads the low flags byte into CL, ORs in `0x40`, loads
the actor info pointer, stores CL back, copies the actor pointer to EAX, loads
`info.painstate` into EDX, then CALLs the setter. The x86 interpreter adds only
the needed instruction families: register-byte OR-immediate (`80 /1`, register
form) and register-to-memory byte MOV (`88 /r`). Unsupported forms still fail
closed. OR produces the modeled logical flags; MOV preserves flags.

The isolated execution theorem is alias-aware and makes no layout assumptions.
In particular, the pain-state number is read **after** the flag store. If that
store overlaps the metadata, the model reads the changed value. Likewise, a
CALL stack slot overlapping the flags really overwrites them. Neither overlap
is silently ignored.

The continuous theorem extends the previous initial relation with metadata
`painstate = 156`, preservation of flags/info/state reads through previous
writes, and separation of the new flag/stack writes from the retained result
fields. Those are initial-state premises. The intermediate relation is derived
from the previous memory frame. The final frame includes the flags word
(conservatively covering the one-byte store) and the return slot.

The player engine does not keep a separate `MF_JUSTHIT` field in its damage
result. The flag theorem specifies the DOS-side update and bit preservation;
it does not claim that a nonexistent Lean field was checked. The live relation
uses `PlayerDamage.apply`'s actual pain result to select the state request.
`Combat.hurtPlayer` uses that result to enter state 156. A small checked theorem
also records that the existing `PlayerAnim.enter 156` yields frame 156, four
tics, and no immediate sound request. Executing the original setter body and
relating its stores to that animation is now covered by the
[pain-setter continuation](PAIN_SETTER_PROOF.md).

## Validation

```sh
./scripts/verify-original-pain-handoff
# With Unicorn and local JIT access:
python3 scripts/verify_original_pain_handoff.py --cross-check
python3 -m unittest discover -s tests -p test_original_pain_handoff.py -v
```

The extraction certificate checks the pinned executable hash, exact bytes,
file mapping, relocations and RNG table. The strict audit covers 29 declarations
and allows only `propext`, `Classical.choice` and `Quot.sound`.

The independent original-byte/live-damage comparison passed all 12,576 cases, covering
all RNG indices on survival, rejection and death, two data relocations, four
alignments, wrapping object pointers and signed damage/health boundaries. It
checks exact ordered byte/word writes, complete dynamic memory, all flag bits,
state-setter arguments, the return slot, RNG state and branch destinations.

Native fixtures cover 9,216 continuous paths, both initially clear and already
set hit flags, unrelated high flag bits, and two deliberate overlap cases.
Separate decoder/execution fixtures cover 8,192 OR cases and 8,192 byte-store
cases across AL through BH, plus truncated/unsupported encodings. Mutation and
contract tests reject altered instructions/table bytes, missing handoff
premises, incorrect skill and invalid axiom audit output. All six focused tests,
five preceding pain-proof tests and eight existing animation-proof tests passed
(19 total). The existing animation proof also rebuilt with the extended decoder.

## Boundary

This proof stops **at setter entry**, before the setter's pushes, state/sprite/
frame/tic stores, action dispatch or RET. It does not yet prove the pain animation
or later pain sound against the original machine. The separate
[pain-setter continuation](PAIN_SETTER_PROOF.md) now covers the non-null,
non-zero-tic, no-action first pain state and connects its return to this call.

Death handling, the remaining damage handler, transport from earlier-tic
initialization, non-environmental damage and whole-game/pixel equivalence remain
open. The ordinary-floor, player-metadata and disabled-tactile contracts remain
in force. The flat x86 model, extraction/loader and Lean compiler/runtime keep
the existing trust boundary. The documented legacy `OriginalDiv`/`OriginalRandom`
API mismatch still prevents claiming a repository-wide test-suite pass.
