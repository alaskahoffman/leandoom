# Fixed-point multiplication parity with original DOOM

**(Lean)DOOM's fixed-point multiplication is formally proved to return the same
32 bits as the original DOOM 1.9 multiplication instructions, for every pair of
32-bit inputs, under an explicit model of those x86 instructions.**

This is a universal equivalence theorem, not a collection of passing examples.
Its domain contains all **18,446,744,073,709,551,616** input pairs. Negative
rounding, `INT_MIN`, and wrapping of oversized results are included, with no
input-range preconditions. The Lean side is the actual engine's `Fixed.mul` in
`Doom/Fixed.lean`; it was not changed to make the proof pass.

## The original bytes

The target is `DOOM.EXE` from the original DOOM shareware 1.9 distribution:

```text
Size:    709905 bytes
SHA-256: b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27

f7 eb          imul ebx
0f ac d0 10    shrd eax, edx, 16
```

`IMUL` interprets EAX and EBX as signed 32-bit integers and puts the full product
in EDX:EAX. `SHRD` shifts bits from EDX into EAX and retains the middle 32 bits
of that product: bits 16 through 47. This is exactly the rescaling and wrapping
needed by signed 16.16 multiplication, including rounding negative fractional
products downward. For example, raw `-1 × 1` returns raw `-1`, not zero.

These six bytes occur at **137 locations in the 32-bit executable code object**.
The first is file offset `0x668d2` (object-relative `0x248be`); the last is
`0x80efa`. The preferred object base is `0x10000`; object offsets are not claims
about the address chosen by a particular DOS loader. The complete file-offset
inventory is pinned in `tests/reference/original-mul.json`.

Independent linear disassembly places all 137 sequences on instruction
boundaries. That is supporting evidence, not a proof that every site is reachable
or an exhaustive classification of all arithmetic in DOOM. id Software's
[published assembly notes](https://github.com/id-Software/DOOM/blob/master/linuxdoom-1.10/README.asm)
also describe the multiply-and-double-shift implementation of `FixedMul`.

## What Lean checks

The proof is in `Doom/Proofs/OriginalMul.lean`. Its public statement is:

```lean
theorem fixed_mul_matches_doom19 (a b : Fixed) :
    (run 2 Doom19.fixedMulBytes (originalMulInputs a b)).map (fun final => final eax) =
      some (a * b).raw.toBitVec
```

`run` **decodes the bytes** and executes two instructions. An unsupported,
truncated, or trailing encoding fails; it is not treated as a no-op. The decoder
supports the register forms of one-operand `IMUL` and immediate `SHRD`, with
32-bit default operand size and no prefixes. It decodes register fields and
masks the shift count according to the instruction definitions.

The instruction semantics in `Doom/Verification/X86.lean` use fixed-width
bitvectors, register writes, a signed full-width product, and a concatenated
register shift. They do not call `Fixed.mul`. The proof independently connects
those operations to the engine's integer product, Euclidean division, and
32-bit conversion. `middle_bits` proves the crucial bit-extraction/division
identity for *every integer product*, using modular arithmetic.

The stronger `original_mul_result` theorem quantifies over **every initial
register state**, including arbitrary initial EDX and unrelated registers.
`original_mul_frame` proves execution succeeds and preserves every register
except EAX and EDX. `original_mul_decode` checks decoding of the literal bytes.

All proofs are checked by Lean's kernel. The audit allows only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms; these new equivalence
proofs use `propext` and `Quot.sound`. There is no `sorry`, custom axiom,
`native_decide`, external solver assumption, or compiled proof-checker axiom.

## Reproduce the evidence chain

Requires the project's pinned Lean 4.33.0 and Python 3. No emulator, disassembler,
SDL installation, or external Lean package is needed for the proof.

```sh
./scripts/fetch-shareware
./scripts/verify-original-mul
```

The verification command is offline. It:

1. Checks the original ZIP and extracted `DOOM.EXE` SHA-256 hashes. It reads the
   split ZIP payload without running the installer or any DOS executable.
2. Checks the embedded MZ/LE headers and maps the executable object's pages.
   Unknown page or relocation formats are rejected. The layout definitions are
   documented in [Open Watcom's LE header](https://github.com/open-watcom/open-watcom-v2/blob/master/bld/watcom/h/exeflat.h).
3. Verifies the 137-site inventory and checks all **10,969 code relocations** for
   overlap with the six instruction bytes. No relocation changes any snippet.
4. Generates `artifacts/original-mul/Extracted.lean` from the **actual extracted
   bytes**, carrying their original file offsets. The generated kernel proof
   checks every snippet equals the proved program and specializes the universal
   result theorem to every extracted site.
5. Compiles the certificate, audits its axioms, and writes
   `artifacts/original-mul/report.json`.

The full executable stays local and is not committed. The repository contains
only the six instruction bytes, provenance metadata, verification code and proofs.

For the project's complete theorem audit and ordinary tests:

```sh
./scripts/test
./scripts/lake env lean ProofAudit.lean
```

Tests intentionally corrupt an instruction, overlap it with a loader relocation,
change the executable identity, and insert additional proof axioms. In particular,
a generated certificate with shift count 15 fails in Lean even when Python's
expected-byte comparison is bypassed.

### Optional independent disassembly and execution checks

```sh
python3 -m venv /tmp/leandoom-binary-tools
/tmp/leandoom-binary-tools/bin/pip install capstone==5.0.6 unicorn==2.1.4
/tmp/leandoom-binary-tools/bin/python scripts/verify_original_mul.py --cross-check
```

Capstone checks all 137 instruction boundaries. Unicorn executes the six bytes
for 196 edge-case pairs and 10,000 deterministic random pairs, varying the other
registers and arithmetic input flags. It checks the result, EDX, preservation of
other registers, and advancement by six bytes. Only the arithmetic snippet is
executed, never the game or installer. These are **independent tests, not the
universal proof**, and neither tool is in the proof's trusted base. On systems
that restrict JIT execution, Unicorn may require permission to allocate executable
memory; the kernel proof does not.

## Exact scope and remaining trust

The x86 model is a small **register-result semantics**, based on the IMUL and
SHRD entries in [Intel's instruction reference](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
It assumes 32-bit operand mode, entry at the start of the six bytes, and completion
of those instructions. It projects away flags, instruction fetch, memory,
interrupts, faults, and timing. Neither instruction reads flags, and neither
modeled encoding has a data-memory operand. This is not a full verified x86 CPU
or a formal refinement of Intel's prose manual.

The theorem checks mathematical execution of the literal bytes. **File I/O,
SHA-256, ZIP extraction, LE mapping, and the correspondence between our instruction
semantics and physical x86 remain outside the kernel proof.** The verifier makes
the file connection repeatable and checks loader relocations, but does not prove
the DOS loader, absence of subsequent self-modification, site reachability, or
surrounding register setup. The generated certificate's hash comment is provenance,
not a theorem about SHA-256. The Lean compiler/runtime and target hardware used
to run the port are also outside this source-level equivalence proof.

This document's theorem specifically establishes **fixed-point multiplication
result parity**. Separate proofs now cover addition, subtraction, the complete
division routine (including its `INT_MIN` quirks and divide errors), and arbitrary
RNG call sequences. See [the arithmetic/RNG proof guide](ARITHMETIC_PROOFS.md).
None of these establishes parity for every engine arithmetic operation, complete
movement/combat ticks, demo synchronization, rendering, audio, or the whole engine.

A precise short description is:

> Our Lean DOOM port has a kernel-checked proof that its fixed-point multiplication
> matches the original DOOM 1.9 machine-code instructions for every input pair,
> under an explicit x86 instruction model.
