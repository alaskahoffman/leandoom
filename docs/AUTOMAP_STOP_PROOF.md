# Original automap shutdown and the DOS notification quirk

Run `./scripts/verify-original-automap-stop`. With Capstone and Unicorn installed,
add `--cross-check` for independent execution of the extracted x86 instructions.
The executable is the pinned shareware DOOM 1.9 image; no game executable or
assets are added to the repository.

The immediate [fixed E1M1 target](E1M1_PROOF_SCOPE.md) uses the live comparison's
inactive automap. These broader shutdown results remain reusable, but extending
keyboard/cheat dispatch is deferred. `E1M1Death.floor_death` instead takes the
inactive branch directly to the death-state setter, under an explicit initial
DOS memory relation.

## What is connected

`DeathAutomapHandoff.execution` starts at the original death guard (`0x2a38c`).
When the dying player is the console player and the automap is active, it follows
that guard's actual CALL to `AM_Stop`, then:

1. Executes `AM_UnloadPics`, including its complete ten-iteration loop.
2. Executes all ten real `Z_ChangeTag2` calls, checking zone magic and the owner
   threshold, writing cache tag 101, and returning to the loop.
3. Returns to `AM_Stop`, clears `automapactive`, and calls `ST_Responder`.
4. Follows the responder branch taken by the notification stored in this DOS
   executable, stopping at its keydown processing entry (`0x39af8`).

The bound is 239 modeled instructions from the death guard, or 226 from
`AM_Stop`. Registers, byte-addressed memory, flags and PC are continuous across
calls and returns. Callees are not replaced with assumed effects. The result is
an explicit machine state, and frame theorems preserve reads disjoint from the
listed writes. Arithmetic and addresses wrap at 32 bits.

This extends the death guard locally. The earlier complete lethal-floor theorem
still ends at `AM_Stop` or `P_SetMobjState`; transporting this new cache contract
from that earlier floor entry remains to be done.

## A detail the binary checks caught

The executable's static notification at data offset `0x12c98` contains the words:

```
0, 1, 0x616d7800
```

`ST_Responder` reads the first word as the event type and the second as `data1`.
Its automap-exit path requires type **1** and data1 **0x616d7800**. The stored DOS
notification therefore takes the **keydown path**, not the automap-exit path.
Both the data extraction certificate and independent x86 runs check this.
The keydown path continues toward cheat handling; that continuation is not yet
proved here. We do not silently shift the pointer or repair the event layout.

There is also a useful, explicitly conditional theorem:
`AutomapStop.stop_execution` proves the entire shutdown and return when memory
contains the exit-event layout expected by the responder. It has a
250-instruction bound, and `AutomapDeathChoice.execution` joins it to the live
`Death.deathState` selector, ending at `P_SetMobjState` within 263 instructions.
It preserves the object pointer, stack convention and disjoint object metadata.
`stop_flags` shows the automap is inactive, shutdown is marked complete, and the
status bar's first-time flag is set, under its separation premise.

**That conditional return theorem does not establish the return path taken by
the stored DOS notification.** Its event premise is deliberately visible, and
negative tests reject substituting the expected event for the extracted one.

## Contracts and trust boundary

The cache contract requires valid zone headers (`0x1d4a11`), owner words at least
256, correct saved registers/return addresses, and the relevant separation
conditions. The ten iterations' requirements are expressed over explicit pure
memory-write constructions derived from the input, rather than assumed callee
execution results. It excludes allocator error paths and corrupt-cache cases.
Frame footprints conservatively include scratch writes and repeated locations;
valid non-overlapping blocks finish with tag 101, also checked independently.

The DOS notification theorem requires its type word to be zero and disjoint
from the intervening writes. The conditional return proof separately requires
the exit-event layout and valid saved-register/return words after the explicit
writes. These contracts are not yet proved from whole-game initialization.

This work adds unsigned JB/JBE/JAE and register XOR on low 16-bit words to the
instruction projection. CMP now records carry as unsigned borrow, and logical
operations record cleared carry. Unsupported flag consumers still fail closed.
The decoder accepts only the specified encodings; no instruction interpretation
is supplied as an axiom.

The certificate binds seven instruction ranges and the stored notification to
extracted bytes and checked LE relocations, then audits 24 declarations. Only
Lean's standard `propext`, `Quot.sound` and `Classical.choice` axioms are allowed;
`sorryAx`, native-evaluation axioms and extra output are rejected.

The flat x86 model, decoder, executable extraction and loader interpretation
remain the stated trust boundary. Segmentation, faults, interrupts, timing,
full compilation correctness, graphics and whole-game equivalence are not
proved by this segment.

## Validation

The independent native check covers 2,048 executions: 1,024 using the stored DOS
notification (half starting at the death guard), and 1,024 using the conditional
exit-event layout (half continuing into death selection). It checks all general
registers, every ordered write, resulting memory, and ten actual allocator calls.
Cases include two data relocation bases, unaligned pointers, wrapping stacks,
repeated cache pointers, unsigned owner boundaries, arbitrary initial register
values, signed health boundaries, and normal/extreme death selection.

Focused regressions reject changed bytes, relocations, notification data,
missing contracts and insufficient execution bounds. Instruction tests cover
carry, unsigned branches, preserved upper register halves and unsupported
encodings. These tests complement the quantified kernel proofs; they are not
an exhaustive whole-game equivalence argument.
