# Original player animation selection and walking-state call

The player-animation suffix now has a kernel-checked proof covering both
original command checks and the actual call to `P_SetMobjState(S_PLAY_RUN1)`.
The selected state and timer match `PlayerAnim.State.startWalking`, the helper
used by `Player.prepareTick`.

For every related suffix-entry state and signed 8-bit forward/side commands:

- No movement command leaves the current animation and timer unchanged.
- A movement command while standing enters state 150, with four tics.
- A movement command in another animation leaves that state and timer unchanged.

There is no ground test here: airborne input still starts walking when standing.
The proof also follows the actual CALL, saved registers, four object stores,
register restoration and RET. It describes the complete resulting machine state
and memory, including the stack words that remain after the stack pointer is
restored. The command-driven helper is a definitionally identical factoring of
the previous runtime expression; gameplay behavior did not change.

## Scope and connection to the engine

`Doom/Proofs/OriginalPlayerAnimation.lean` contains:

- `selector_program`: both command checks, the standing-state check, and the
  actual call instruction or skipped-call path.
- `call_establishes_setter`: derives the callee's complete input relation from
  the suffix-entry relation, including the return address written by CALL.
- `setter_program`: the executed walking-entry path, split into prologue, body
  and epilogue. The original state-table entry has a null action and nonzero
  tics, so no action callback or zero-tic loop is taken.
- `animation_bytes`: the continuous original caller/callee execution, with no
  reset at the call boundary, ending just before the player's function epilogue.
- `animation_engine`: final encoded animation state and tics match the actual
  runtime helper, and the stack pointer equals its suffix-entry value.

`Inputs` states the table values and byte-range separation needed to preserve
lookup data and saved stack words. `EngineInputs` additionally relates command
bytes, the state pointer and tics to the Lean animation. Its state-index bound
is 65,536, which prevents pointer-encoding wraparound; this is a representation
bound, not a claim that DOOM has that many real animation states.

The [joined player proof](PLAYER_JOINED_PROOF.md) now derives this suffix
relation from one pre-turn relation and retains the complete machine state
from turning and both thrusts. The local suffix theorem remains useful on its
own with an animation-entry relation. The original player function's wrapper,
other state-setter paths, collision and full-tic equivalence remain outside
these theorems.

## Bytes, table and machine semantics

The certificate checks two original regions from the pinned shareware DOOM 1.9
executable (SHA-256
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`):

| Region | Code-object offset | File offset | Size |
| --- | --- | --- | --- |
| Animation caller | `0x3323e` | `0x75252` | 32 bytes |
| State setter | `0x30ea0` | `0x72eb4` | 91 bytes |

Both data-operand relocations are checked. Extraction also checks the 28-byte
RUN1 table entry at data offset `0x16a90`: sprite 28, display frame 0, tics 4,
null action, next state 151, and two zero miscellaneous fields. There are no
relocations inside this table entry.

`X86Routine` extends the previous instruction semantics with the byte compare,
immediate operations, stack operations and relative CALL/RET needed here.
Programs use absolute DOS code-object offsets: callee entry
is `0x30ea0`, caller entry is `0x3323e`, and the return/exit PC is `0x3325e`. CALL writes
that following PC to byte memory; RET obtains its destination by reading memory.
Unsupported paths fail closed. The decoder includes only the encodings needed
for this proof; it does not model arbitrary x86 or every state-setter path.

The model uses flat total memory and immutable code. Code/data loading,
segmentation, faults, interrupts, physical timing and Lean compilation/runtime
remain outside the proof. Extracted table identity and independent emulator
comparisons are external checks, not additional proof axioms.

## Validation

```sh
./scripts/verify-original-player-animation
python3 -m unittest discover -s tests -p 'test_original_player_animation.py'
# Optional: Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_player_animation.py --cross-check
```

The certificate permits only `propext`, `Classical.choice` and `Quot.sound`.
It rejects proof holes, unchecked native checker axioms and incomplete audits.

The independent run passed **196,608 x86 comparisons**: all 65,536 command pairs
from each of standing and running, plus every 16-bit initial state index with
varied commands and timers. It uses two data relocation bases and unaligned
objects/stacks, checking all registers, flags, the full dynamic memory page,
store order, animation fields and execution of the real CALL/RET path.

Eight new tests cover byte/table/relocation corruption, proof auditing, call and
return memory behavior, stack wraparound, unsupported instructions, the derived
callee relation and the runtime helper's original condition. Six existing
motion-proof tests and 89 fidelity regressions also pass, as do 98 built-in
engine checks. The game and interaction proofs rebuild. No full gameplay replay
was rerun for this proof and behavior-preserving refactor.
