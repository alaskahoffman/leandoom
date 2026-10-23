# Original caller to P_MovePlayer, including return

`PlayerCaller.observation` connects the original `P_PlayerThink` movement call
site to the complete movement-function proof. It starts before the caller
copies its player pointer into the argument register, executes the real CALL,
runs all of `P_MovePlayer` and its selected walking-state call, returns, and
executes the caller's argument reload for the subsequent height calculation.

Under the explicit call-site input relation, final angle and momenta match
`Motion.movePlayer cmd`, and animation state and timer match
`anim.startWalking cmd`. The caller's ESP, EBX, ECX, EDX, ESI, EDI and EBP are
unchanged, and EAX contains its original EDX player pointer, ready for the next
call. The initial value of EAX is unrestricted.

This proves the selected movement call site, not every path through
`P_PlayerThink`. The earlier reaction-time decision and the later height
calculation remain outside the theorem, as does establishing the input relation
for all reachable whole-game states.

## What the caller now establishes

The exact nine-byte region is:

```text
0x333c2  MOV EAX, EDX
0x333c4  CALL 0x33160       ; P_MovePlayer
0x333c9  MOV EAX, EDX
0x333cb                    ; next CALL, outside this result
```

PCs now use absolute DOS code-object offsets. Execution starts at PC `0x333c2`,
CALL saves `0x333c9`, and the final observation is at `0x333cb`. The return word
is written by the actual CALL instruction. It is not supplied as a new
assumption or inserted by a testing harness in the formal proof.

`establishes_function` derives every `PlayerFunction.Inputs` field from the
call-site relation. It accounts for the caller's return-address store before
the movement function saves its own registers. The proof shows that store
preserves the player pointer, commands, motion fields, animation fields and
lookup tables needed by the function. It transports the existing memory/layout
invariants and derives the concrete return-address condition.

The `layout` view describes initial data with EAX identifying the caller's EDX
player pointer and ESP identifying the future scratch slot, 32 bytes below
the caller's ESP. Like the earlier `frameView`, this only expresses a contract
on initial memory. The theorem executes the actual MOV, CALL, prologue, body,
epilogue, RET and reload without resetting the machine state at any boundary.

The relation still requires the caller's data to encode the specified Lean
motion, animation and command values, with the stated tables and nonaliasing
layout. This milestone discharges the local calling-convention and stack-store
obligations; it does not yet prove those global data invariants from game startup.

The proof reuses the complete movement theorem unchanged. The bound is 120
instructions: two caller instructions before the function, the previous
117-instruction function bound, and one caller instruction after return.
The selected animation branch includes a second, nested CALL/RET.

## Original-byte certificate

Extraction checks all three regions against the pinned shareware executable:

| Region | Original code | File offset | Bytes |
| --- | --- | --- | --- |
| Caller | `0x333c2` | `0x753d6` | 9 |
| P_MovePlayer | `0x33160` | `0x75174` | 264 |
| State setter | `0x30ea0` | `0x72eb4` | 91 |

The eight data relocations in the function/setter are validated; the caller's
relative CALL has no data relocation. Executable SHA-256:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

The certificate audits execution, runtime observations, entry-relation
derivation, the CALL-written return address, restored registers, and the
post-return player argument. Only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Byte equalities use no axioms. No proof holes or unchecked native
checker axioms are accepted.

The same machine-model boundaries apply: flat total memory, immutable code,
partial flag semantics, and explicit code/data address conventions. DOS loading,
segmentation, faults, interrupts, physical timing and Lean compilation/runtime
are not proved. The walking state setter remains restricted to the path this
function selects.

## Validation

```sh
./scripts/verify-original-player-caller
python3 -m unittest discover -s tests -p 'test_original_player_caller.py'
# Requires Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_player_caller.py --cross-check
```

The independent harness enters at the caller's first MOV, with the player in
EDX and an arbitrary EAX. It does not preinstall a movement-function return
address. The original CALL writes it. The run stops after the caller reloads
EAX, just before the next call, checking the full dynamic memory page, ordered
writes, all registers, final flags, cached ground and both call/return levels.

Cases cover all 65,536 turn encodings, all forward/side command pairs from
standing and running, and additional airborne cases. Heights, angles, momenta,
timers, registers and initial flags vary. Player/object/stack addresses include
unaligned layouts, and the harness uses two data relocation bases.

The seven new tests cover mutations of the argument register, call target and
reload; strict axiom auditing; derivation of function/body relations; rejection
of missing stack-preservation premises; derivation of the return address with
no premise; restored caller stack and next argument; and pinned extraction with
relocation validation. Existing function and fidelity regressions are retained.

All **199,168 caller/function x86 comparisons** passed, along with the
certificate/axiom audit, **103 targeted Python tests** (7 caller, 7 function,
89 fidelity), and the interaction proof build. No gameplay behavior changed
and no complete gameplay replay was rerun.

## Next boundary

The [reaction-time proof](PLAYER_REACTION_PROOF.md) now includes the preceding
object/timer loads and both the decrement-and-skip branch and this movement
call. The following `P_CalcHeight` routine now has a
[complete function and call-site proof](PLAYER_HEIGHT_PROOF.md). The reaction
result establishes the height-call entry contract, including cached ground;
`PlayerPreparation.observation` now composes both into one uninterrupted
shared-origin execution. `PreparedState` now proves the eleven preparation
fields and a combined memory frame; `PreparedRuntime` connects that projection
to the actual `Player.prepareTick`. Whole-caller reachability, the complete
player/world-state relation and later player actions remain separate obligations.
