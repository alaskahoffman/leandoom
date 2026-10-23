# One pre-turn relation for player motion and animation

Turning, the ground/command checks, both conditional thrusts, animation
selection and the actual walking-state CALL/RET now form **one uninterrupted
original-byte execution theorem**. The caller starts before turning and stops
immediately before the `P_MovePlayer` epilogue.

`PlayerJoined.joined_observation` proves that the final angle and both momenta
match `Motion.movePlayer cmd`, and the final encoded animation state and timer
match `anim.startWalking cmd`, the helper used by `Player.prepareTick`. The
command is unchanged. The final stack pointer equals the pre-turn stack pointer.

The theorem is universal over inputs satisfying the explicit initial relation.
There are no new premises about the machine state at the motion/animation seam
or at the state-setting call. This does not yet prove that every reachable game
state establishes that initial relation.

## What was joined

The previous motion theorem retained only selected output observations. The
new `OriginalMotionState.lean` strengthens it to identify the entire output
state, including registers and flags. It reuses the existing checked instruction
paths and arithmetic summaries; it does not substitute a newly initialized
machine state at the boundary.

`X86RoutineBridge.lift_control_prefix` transports that exact executed path into
the call-capable machine, translating only the PC to the shared code origin.
For each executed instruction it requires matching decoding, matching control
semantics, and that the enclosing program has not already exited.

`PlayerJoined.establishes_animation` derives the existing animation input
relation from the single pre-turn `PlayerJoined.Inputs` relation. It proves:

- ECX still identifies the same player, ESI the same command bytes, and ESP
  the same stack position.
- The player pointer, command bytes, animation fields and RUN1 table entries
  survive the preceding angle, cached-ground, scratch and momentum stores.
- The table/stack separation needed by the actual call remains valid.

The final observation also proves the other direction of preservation: the
animation call's stack and object writes leave the newly computed angle and
momenta intact. The standing/running decision and timer are thus joined with
the motion results, not merely checked in isolation.

`joined_execution` identifies the full final register/memory state.
`joined_observation` projects the angle, momx, momy, animation-state pointer,
tics, final PC and stack pointer and connects them to the runtime functions.

## Bytes and assumptions

The certificate binds a **245-byte contiguous caller region** beginning at
original code offset `0x33169` / file offset `0x7517d`, plus the **91-byte state
setter** at `0x30ea0` / file offset `0x72eb4`. It checks all eight data-operand
relocations. The pinned shareware DOOM 1.9 executable SHA-256 is:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

PCs now use absolute DOS code-object offsets: execution begins
at PC `0x33169`, reaches animation at `0x3323e`, and exits at `0x3325e`. A fuel
bound of 102 instructions is sufficient; individual branches execute fewer.
The walking call reads and writes its real return address through stack memory.

`Inputs` extends the prior motion relation with the initial animation state,
timer, table values and bytewise separation from the stores that would corrupt
later reads or final motion observations. All of these concern initial data
and layout; none assumes the requested equivalence or an intermediate result.

As before, the model uses flat total memory, immutable code and explicit
code/data address conventions. DOS loading/segmentation, faults, interrupts,
physical timing and Lean compilation/runtime remain outside the proof. The
state setter is verified for the walking-entry path selected here, not for
arbitrary action callbacks or zero-tic animation chains.

## Validation

```sh
./scripts/verify-original-player-joined
python3 -m unittest discover -s tests -p 'test_original_player_joined.py'
# Optional: requires Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_player_joined.py --cross-check
```

The extraction certificate audits the full-state theorem, runtime observation,
input derivation, preservation and machine bridge. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Proof holes and unchecked
native checker axioms are rejected.

The comparison harness executes the caller and callee with a single emulator
run per case. All **199,168 comparisons passed**. It covers all turn encodings with varied heights and animations,
all forward/side command pairs from standing and running, and additional
airborne cases. It compares the compiled runtime functions and checks the full
dynamic memory page, all registers, flags, cached ground, scratch/stack words,
write order and the actual call/return path. Two data relocation bases and
unaligned player, object and stack addresses are exercised. Original sine-table
entries and the RUN1 entry are checked separately during extraction.

The six new tests cover exact bytes and relocations, strict axiom auditing,
deriving animation and callee inputs, refusing omitted preservation premises,
and retaining final motion fields across the real animation stores. Eight
existing animation tests and 89 fidelity regressions also pass. The interaction
proof still builds. Only proofs, diagnostic tooling and documentation changed;
no gameplay behavior changed or complete gameplay replay was rerun.

## Next boundary

The [complete-function proof](PLAYER_FUNCTION_PROOF.md) now includes the
original prologue and epilogue and derives this theorem's relation through the
prologue. The caller's responsibility for establishing the function-entry
relation, collision, position integration, the rest of a tic and whole-game
correspondence remain outside these results.
