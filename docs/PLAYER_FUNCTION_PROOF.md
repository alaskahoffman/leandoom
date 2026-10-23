# Original P_MovePlayer: first instruction through return

`PlayerFunction.observation` proves correspondence for the **complete original
DOOM 1.9 `P_MovePlayer` function**, under an explicit function-entry relation.
The run starts at the first `PUSH` and finishes after the final `RET`, including
the actual walking-state call and return when that branch is selected.

For every input satisfying that relation, the final angle and momenta equal
`Motion.movePlayer cmd`; animation state and timer equal `anim.startWalking cmd`,
the helper used by `Player.prepareTick`. EBX, ECX, EDX, ESI, EDI and EBP are
restored to their entry values. ESP advances four bytes past the original
return address, and execution returns to the address read from entry memory.
EAX is a clobbered register, as in the original function.

This is a universal conditional theorem, not a count of passing test cases.
It does not yet establish the entry relation for every reachable caller state,
or prove a whole tic or whole-game correspondence.

## Closing the stack boundary

The nine-byte prologue saves six registers and allocates a four-byte scratch
word. Its six stores are proved not to alter the data required by the previous
motion/animation theorem. `establishes_body` derives that theorem's entire
input relation from the function-entry relation; no body-entry memory state
is supplied as an additional premise.

`frameView` is a convenient way to express the entry contract: it keeps the
original entry memory and register values, except that ESP identifies the
future scratch slot, 28 bytes below entry ESP. This is only a predicate-building
view. The execution theorem runs the real pushes and stack adjustment, and
uses their actual memory as the body input.

The body preserves the six saved words and the return-address word. The
10-byte epilogue releases the scratch word, pops the registers in reverse
order, and reads the original return address through ordinary stack memory.
The proof retains stack writes in its full memory result; popping does not
erase them. Word-slot separation also holds across 32-bit address wraparound.

The previous body proofs are reused. `transport_inputs` supplies a reusable
way to carry their input relation across memory updates that preserve its
read footprint. The proof is composed from a seven-instruction prologue,
the existing body with a 102-instruction bound, and an eight-instruction
epilogue. The total bound is 117 instructions; shorter paths exit earlier.

## Binding to the original executable

The extraction certificate checks the entire **264-byte / 93-instruction**
function at original code offset `0x33160` through `0x33267`, file offset
`0x75174`, plus the existing 91-byte state setter at `0x30ea0`. It validates all
eight data-operand relocations. The pinned shareware executable SHA-256 is:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

Code PCs now use absolute DOS code-object offsets. Function entry
is `0x33160`, body entry `0x33169`, and epilogue entry `0x3325e`. The contract
requires the saved return PC to be at least `0x33268`, outside the verified
regions. Establishing the actual caller's return address is still an external
obligation; the theorem does not choose or overwrite it.

The decoder now supports the register forms of signed-byte immediate ADD/SUB
used by the stack adjustments. Their register effects are modeled, and their
flags are invalidated in the abstraction. Unsupported memory-writing forms
remain unsupported. The earlier comparisons still use explicitly modeled
flags where branch decisions require them.

The machine model retains its existing boundaries: flat total byte memory,
immutable code and explicit code/data address conventions. DOS loading,
segmentation, faults, interrupts, physical timing, and Lean compilation/runtime
are not verified here. The state setter is covered for the walking-entry path
selected by this function, not arbitrary callbacks or zero-tic state chains.

## Reproducing the checks

```sh
./scripts/verify-original-player-function
python3 -m unittest discover -s tests -p 'test_original_player_function.py'
# Requires Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_player_function.py --cross-check
```

The certificate audits the execution and runtime-observation theorems, the
entry-relation derivation, register restoration, return address, and memory
transport theorem. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed; proof holes and unchecked native-checker axioms are rejected.

The independent comparison runs the actual function and its state setter in
one continuous x86 execution. It covers all signed-16-bit turn encodings,
all forward/side byte pairs from standing and running, and additional airborne
cases. Initial angles, momenta, timers, other registers and flags vary; player,
object and stack addresses include unaligned cases, with two data relocation
bases and multiple return addresses. It checks the compiled runtime fields,
full dynamic memory page, all registers, cached ground, stack contents,
write order, final flags, and both levels of call/return.

Seven new tests cover byte mutations in saves, allocation, restoration and RET;
strict axiom auditing; deriving body and animation relations; rejecting missing
stack-preservation obligations; the return/register contract; all 4,096 signed
immediate ADD/SUB register encodings; and exact extraction/relocations.

Validation completed with **199,168 whole-function x86 comparisons**,
**110 targeted Python tests** (7 function, 6 joined-body, 8 animation and
89 fidelity), and the interaction proof build. The certificate's axiom audit
passed. No gameplay behavior changed, and no full gameplay replay was rerun.

## Next boundary

The [caller proof](PLAYER_CALLER_PROOF.md) now connects the actual MOV/CALL
at `0x333c2`/`0x333c4`, the complete function, its return to `0x333c9`, and the
following argument reload. It derives this function's entry relation and return
address from a call-site data/layout relation. Establishing that relation from
all reachable states is still separate. Next are the preceding reaction-time
branch and subsequent `P_CalcHeight` call; collision and position integration
happen elsewhere and need their own correspondence results.
