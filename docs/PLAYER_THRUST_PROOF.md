# Original player thrust and reusable block summaries

`Doom/Proofs/OriginalThrust.lean` proves that the 17-instruction body of the
original shareware DOOM 1.9 `P_Thrust` produces exactly the momentum computed by
the real engine's `Motion.thrust`, for every input satisfying the explicit
memory/state relation. It also specifies the entire final memory: exactly the
two momentum words are written, in original order.

This is a local theorem in a flat, data-object-relative x86 model. It is not a
complete player-update, DOS loader, or whole-game equivalence theorem. No game
behavior was changed for this proof; `Motion.thrust` remains the existing engine
implementation.

## What is now reusable

`Doom/Verification/X86Block.lean` decodes supported straight-line byte sequences
into operations and provides an execution/composition model. Unsupported
instructions, prefixes, truncated operands, trailing bytes and wrong instruction
counts fail. It extends the existing register and memory models with logical
right shift and 32-bit ModRM/SIB addressing for loads and LEA. No unrecognized
operation is silently skipped.

`Doom/Proofs/BlockSummary.lean` supplies:

- `certified`: connects the byte decoder to symbolic execution with summaries.
- `multiply_correct`: reuses `original_mul_result`, with the complete modeled
  register effect, for the original IMUL/SHRD pair.
- `summarized_correct`: proves that substituting this summary inside any decoded
  instruction list preserves the complete modeled state.
- `eval_append` (in `X86Block`): composes decoded blocks without expanding their
  internals again.
- `summarize_x86`: reduces the closed decoder output and simplifies the symbolic
  state with these proved rules. It does not require a handwritten disassembly.
- Byte-memory load/store and separation lemmas, including unaligned and wrapping
  addresses.

The original thrust memory summary is checked with:

```lean
  rw [certified _ _ _ thrust_decoded]
  dsimp only [thrustMemory]
  summarize_x86 thrustOps
```

`thrustMemory` is a proposed summary, not a trusted specification: the tactic
must prove it agrees with the decoded instructions. The arithmetic proof is
reused twice. The same tooling is also tested against the earlier turning block.
This is a small extensible automation layer, not a general decompiler or an
automatic whole-program equivalence checker. The memory relation and the
connection to `Motion.thrust` still required manual proofs.

## The claim and its assumptions

The extracted block is code-object offset `0x32ff4`, file offset `0x75008`,
55 bytes. It begins after the four register pushes and ends before the pops and
RET. At entry EAX is a player pointer, EDX is the binary angle, and EBX is the
signed 16.16 thrust amount. Player+0 points to the map object; map-object+72 and
+76 are horizontal momentum.

The theorem covers every 32-bit angle, thrust amount and initial momentum,
including negative values and wrapping overflow. It is not restricted to the
values in a recorded playthrough or to the smaller normal controller range.

`ThrustInputs` relates those registers and memory fields to Lean values. Its two
separation clauses require that the first momentum write does not overwrite:

1. the player-to-object pointer, which the original reads again;
2. the selected sine entry, which the original reads after its first write.

The raw `original_thrust_memory` summary needs no such separation assumptions:
it preserves the actual read/write ordering even when addresses overlap. They
are needed to connect that low-level behavior to the structured Lean state.
The two adjacent momentum words are proved disjoint for all wrapping addresses.

`thrust_table_index` proves that SHR by 19 followed by scaling by 4 selects the
same index as `Angle.fineIndex`. `thrust_selected_tables` derives both lookups
from one full-table memory invariant, and `ThrustInputs.of_tables` packages this
for callers. Establishing and preserving that invariant during whole-game
initialization/execution remains an obligation.

## Relocations and trust boundary

The on-disk instructions contain two data-object-relative operands:
`0x13584`, the cosine-pointer cell, and `0x5a84`, the sine table. The cosine
pointer's initial value is `0x7a84`, 2048 entries into the same table.

The verifier checks the LE mapping, both code operand relocations, the pointer's
data relocation, and the absence of relocations inside the sine table. A fixup
crossing a page boundary is listed twice by LE; it is deduplicated by its exact
source/object/target identity.

The theorem runs the on-disk operands with a memory model in those relative
coordinates. It does **not** prove that a particular DOS loader's rebased
execution corresponds to this model. The optional emulator tests exercise two
load bases, but those tests are not a relocation theorem. Loader/segment
correspondence is an explicit remaining link.

Also outside this theorem: stack saves/restores, return control, EFLAGS, access
faults, instruction fetch, interrupts, physical timing, caller invariants,
forward/side-thrust sequencing, collision, the Lean compiler/runtime, and the
physical CPU's implementation of the modeled instructions. Memory is total and
flat; the theorem does not prove physical memory accessibility.

No `sorry`, custom axioms or native-evaluation shortcuts occur in the checked
certificates. The audited claims depend only on `propext` and `Quot.sound`; the
extracted-byte identity depends on no axioms. Executable identity, archive
extraction, LE parsing and table comparison are external checks.

## Reproduction and validation

With the pinned shareware archive installed:

```sh
./scripts/verify-original-thrust
```

This builds the proof and probe, extracts the original block, generates
`artifacts/original-thrust/Extracted.lean`, checks its proof and axiom audit,
and compares all 10,240 original sine-table entries with the compiled engine.
The final report is `artifacts/original-thrust/report.json`.

Optional independent Capstone/Unicorn checks:

```sh
/private/tmp/leandoom-binary-tools/bin/python scripts/verify_original_thrust.py --cross-check
```

The initial independent run passed 35,169 cases: four low-bit positions in every
one of the 8192 fine-angle bins, plus combinations of extreme values. Tests use
full-width thrust/momentum, unaligned objects and two data load bases. They check
both momentum results against the compiled `Motion.thrust`, all eight general
registers, the entire mapped dynamic-memory page, and the exact write addresses
and order.

Regression tests reject changes to the angle shift, table address and momentum
write address; reject false summaries; check decoding failures and composition;
and verify the complete table comparison rejects corruption. Run:

```sh
python3 -m unittest discover -s tests -p test_original_thrust.py -v
```

## Next boundary

This establishes reuse on straight-line blocks. Conditional branches, flags,
stack/call contracts and loop invariants are not yet supported by this block
layer. A useful next composition target is the original `P_MovePlayer` sequence:
turn, ground check, forward thrust, side thrust, and animation update, with each
call's state relation discharged rather than assumed. That requires extending
the control-flow model; this proof alone does not establish that sequence.
