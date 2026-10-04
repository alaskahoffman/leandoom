# Core arithmetic and RNG parity with original DOOM 1.9

The port's **four core fixed-point operations and random-number generator have
kernel-checked equivalence proofs against extracted DOOM 1.9 instruction bytes**,
under explicit, small x86 semantics. These are universal theorems about the real
Lean engine functions, not proofs of a duplicate implementation or claims based
on sampled tests.

| Operation | Proven claim | Lean theorem |
| --- | --- | --- |
| Addition | Identical wrapping 32-bit result for every input pair | `fixed_add_matches_doom19` |
| Subtraction | Identical wrapping 32-bit result for every input pair | `fixed_sub_matches_doom19` |
| Multiplication | Identical rescaled 32-bit result, including negative rounding and overflow, for every input pair | `fixed_mul_matches_doom19` |
| Division | Same returned bits or divide-error cause for every input pair; includes the guard and both return paths | `fixed_div_matches_doom19` |
| RNG | Same returned values and both final indices for any finite sequence of play draws, misc draws and resets | `random_trace_matches_doom19` |

Each binary arithmetic theorem covers **2^64 operand pairs** without range
preconditions. The RNG theorem covers arbitrary trace length and any matching
initial pair of valid byte indices. It assumes the same calls in the same order;
it does not prove that the entire game makes those calls at the same times.

The proof files are `Doom/Proofs/OriginalAddSub.lean`, `OriginalMul.lean`,
`OriginalDiv.lean`, and `OriginalRandom.lean`. `ProofAudit.lean` prints their
axiom dependencies. Only the standard `propext`, `Classical.choice` and `Quot.sound`
are allowed. There are no unfinished proofs, custom axioms, native evaluation
axioms, or external solver assumptions.

## A real behavior correction: division at INT_MIN

Previously `Fixed.divChecked` rejected every pair containing `INT_MIN` because
the C reference's `abs(INT_MIN)` is undefined. The original binary resolves this:
its XOR/subtract absolute-value sequence wraps and leaves `INT_MIN` negative.
Its guard uses a signed arithmetic shift and signed comparison. Some edge inputs
saturate, some divide successfully, and some reach an x86 divide error (#DE).

The engine now implements those distinctions. A DOS CPU exception is represented
as an explicit Lean `Except` result, rather than crashing the host process:

| Raw numerator | Raw denominator | Original routine / Lean outcome |
| ---: | ---: | --- |
| `-2147483648` | `65536` | `-2147483648` |
| `-2147483648` | `-65536` | quotient overflow / `DivisionError.quotientOverflow` |
| `-2147483648` | `0` | zero divisor / `DivisionError.divideByZero` |
| `-2147483648` | `-65537` | `2147450880` |
| `-2147483648` | `-2147483648` | `2147483647` (the historical guard saturates) |
| `0` | `0` | `2147483647` (the guard prevents IDIV) |

Both error causes raise #DE on x86; the model distinguishes their conditions.
This proves arithmetic results/faults, not parity with the DOS exception handler
or host error presentation. Ordinary inputs continue to match the C reference.
`Fixed.div?` remains a diagnostic helper with different semantics and is **not**
covered by the division parity claim. Other helpers that reject an unverified
absolute-value domain are not automatically covered by this division theorem.

## What ties the proofs to the original executable

The target is the 709,905-byte `DOOM.EXE` from the original shareware 1.9 ZIP:

```text
SHA-256 b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27
```

`tests/reference/original-arithmetic.json` records the literal bytes, file
offsets and data relocation targets. No full executable or game assets are
committed. The relevant file offsets are:

| Snippet/data | File offset | Length |
| --- | --- | ---: |
| `ADD EAX, EBX` | `0x62ba1` | 2 |
| `SUB EAX, EBX` | `0x62baa` | 2 |
| Complete `FixedDiv` routine | `0x5f194` | 65 |
| Gameplay RNG routine | `0x66174` | 28 |
| Miscellaneous RNG routine | `0x66194` | 28 |
| RNG reset routine | `0x661b4` | 17 |
| Shared random table | `0x9a630` | 256 |

The addition/subtraction examples are real instruction boundaries in executable
code; their result semantics also apply to the same instruction forms elsewhere.
They are not a classification/proof of every addition or subtraction call site.
The [multiplication verifier](BINARY_PROOF.md) separately checks 137 inlined sites.

The division and RNG proofs use a byte decoder plus instruction semantics in
`Doom/Verification/X86Routine.lean`. Control-flow listings accelerate the proofs,
but every executed listing entry is checked against the decoder. A generic
`runProgram_sound` theorem connects successful listing execution (including
modeled divide errors) to execution of the original byte list. The final theorems
are stated on the **byte interpreter**, not just on the listings.

The random table is extracted independently of `Doom.randomTable`; a kernel proof
checks all 256 entries agree. Another proof connects each machine-code call to the
engine's actual `nextPlay`, `nextMisc` or `clear`. Induction composes those results
into arbitrary call traces, including index wraparound and interleaved resets.

RNG instructions contain addresses changed by the loader. The verifier checks
the exact relocation records: each expected operand is an internal absolute
dword reference to data object 3 with the recorded target offset. It checks the
RNG table's LE page mapping and verifies no relocation changes the table. The
model uses data-object-relative addresses; the emulator independently relocates
those operands into its actual mapped data region.

## Reproduce

```sh
./scripts/fetch-shareware
./scripts/verify-original-mul
./scripts/verify-original-arithmetic
./scripts/lake env lean ProofAudit.lean
```

Verification is offline after fetching shareware. It checks archive and executable
hashes, code/data page mappings and relocations, then generates
`artifacts/original-arithmetic/Extracted.lean` using bytes read from the executable.
The generated add/sub/division theorems and arbitrary RNG-trace theorem use these
extracted bytes and table. Lean checks the certificate and its axiom audit before
the verifier writes `report.json`.

The normal `./scripts/test` suite builds the proofs and includes negative tests
that alter the division branch, replace ADD with SUB, and change an RNG table
entry. Each altered certificate must fail in the kernel, even when the Python
expected-byte comparison is deliberately bypassed.

Optional independent tests against the **compiled** engine:

```sh
python3 -m venv /tmp/leandoom-binary-tools
/tmp/leandoom-binary-tools/bin/pip install capstone==5.0.6 unicorn==2.1.4
/tmp/leandoom-binary-tools/bin/python scripts/verify_original_arithmetic.py --cross-check
```

Capstone checks disassembly; Unicorn runs only these snippets/routines. Arithmetic
cases include signed extrema, guard boundaries, divide errors and seeded random
inputs. RNG testing keeps original machine memory across thousands of interleaved
calls, wraparounds and resets. All values and indices are compared with
`fidelity-probe`, which calls the actual compiled Lean engine. Emulator state is
restored between arithmetic cases, including after CPU faults. These tests are
supporting evidence; the universal proofs do not depend on either tool.

## Scope and trust

The ISA models are based on the instruction descriptions in the
[Intel SDM](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
They model 32-bit register operations, the division branch condition, relevant
data accesses, saved registers on an abstract call-local stack, and routine
return. Undefined/unneeded flags are not invented. Unsupported encodings or
conditional reads of unknown flags fail explicitly.

They assume valid instruction entry, 32-bit operand mode, available stack/data,
an unchanged read-only table, and no external interference. The writable index
dwords and table bytes occupy disjoint modeled regions. Physical stack addresses,
segmentation, fetch faults, interrupts, timing and the DOS loader/exception handler
are outside this model. It is not a complete verified CPU model or a formal
derivation of Intel's prose specification.

SHA-256, ZIP extraction, file I/O, LE mapping and relocation checks are external
evidence, not kernel-proved filesystem facts. Correspondence of our instruction
model to physical x86, and the Lean compiler/runtime that executes the port, remain
trust assumptions. Independent emulator checks help detect modeling errors but
do not discharge these assumptions.

The accurate claim is **core fixed-point arithmetic and RNG sequence parity under
the documented x86 model**. This does not prove every engine arithmetic helper,
whole-game random-call order, movement/combat equivalence, demo synchronization,
rendering/audio fidelity, or complete DOOM compatibility.
