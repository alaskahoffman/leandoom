# Original inlined player thrust

The forward and sideways thrust bodies inside the pinned DOS DOOM 1.9
`P_MovePlayer` now have universal Lean proofs connecting their actual bytes to
`Motion.thrust`. This covers every signed 8-bit command, 32-bit angle and pair of
32-bit momenta satisfying the stated memory relation. It is a local component
proof, not yet a proof of the complete player update or whole game.

## The bytes and result

| Body | Code-object offset | EXE file offset | Bytes | Instructions |
| --- | --- | --- | --- | --- |
| Forward | `0x33199` | `0x751ad` | 72 | 23 |
| Sideways | `0x331f1` | `0x75205` | 77 | 24 |

The EXE SHA-256 is
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
Extraction verifies the original slices, file mappings and both LE data-operand
relocations in each block. A generated certificate checks the extracted bytes
against the byte lists used by the proofs.

The code is genuinely inlined: the player update does not call the separately
proved `P_Thrust` body. `OriginalInlineThrust.lean` decodes and proves these two
additional instruction sequences. Their arithmetic reuses the existing
multiplication and standalone thrust theorems.

The forward body sign-extends DL and multiplies it by 2048. The sideways body
sign-extends DH, applies the same scaling, and subtracts a quarter turn from the
angle with 32-bit wraparound. Both select the original fine-angle table entries
and add the two fixed-point products to momentum. `command_thrust_exact` proves
that the sign-extension/shift agrees with the actual engine's command scaling.

Both bodies also write the fine-angle byte index to `[ESP]`. The theorem retains
that write: the entire resulting memory equals the original memory with the
scratch word and the two engine-computed momentum words written in original
order. The raw instruction summaries preserve overlapping-memory behavior
without separation assumptions. The engine correspondence explicitly requires
that scratch and momentum writes do not corrupt subsequent input reads.

## Reuse and assumptions

`inline_reuses_thrust` relates the new instruction summaries to the existing
standalone thrust memory summary. It constructs a mathematical input state for
that summary; it does not claim the original executable makes a function call.

`InlineThrustInputs` relates the command byte, angle and momenta to the Lean
values. It also requires the shared `ThrustTables` invariant and byte-range
separation for the relevant player pointer, scratch word, table entries and
momentum fields. `inline_thrust_inputs` proves that these entry obligations
survive the scratch write and satisfy the existing thrust theorem's premises.
The verifier independently compares all 10,240 original sine-table entries with
the compiled Lean table; establishing the invariant from a verified DOS loader
remains an external obligation.

The decoder additions are memory MOV stores, register-byte MOVSX (including the
high byte registers), and immediate SUB EAX. Stores and MOVSX preserve modeled
flags; SUB invalidates them until a separately modeled instruction establishes
new flags. These thrust proofs observe memory, not outgoing flags.

## Reproduce

After fetching shareware:

```sh
./scripts/verify-original-inline-thrust
python3 -m unittest discover -s tests -p 'test_original_inline_thrust.py'
```

For additional independent Capstone/Unicorn checks, use a Python environment
with those optional packages:

```sh
python3 scripts/verify_original_inline_thrust.py --cross-check
```

The initial independent run passed **36,352 cases**, 18,176 per body. Coverage
includes all 8,192 fine-angle bins at two low-bit boundaries, all 256 command
bytes, quarter-turn and signed-angle boundaries, random full-width momenta,
two data relocation bases, and unaligned player/object/scratch addresses. Each
case checks all eight general registers, the full dynamic memory page, and the
three write addresses in order. This is empirical validation of the instruction
model against an independent emulator, not an exhaustive test of all states.

The certificate's byte identities depend on no axioms; its main proofs depend
only on Lean's `propext` and `Quot.sound`. The verifier rejects missing audits,
`sorryAx`, native-checker axioms and unexpected output. Regression tests also
reject changed command-register, scratch-address and angle-adjustment bytes,
and exercise malformed instruction and flag-preservation boundaries.

## Still to prove

The [turning and forward guard](PLAYER_MOVE_ENTRY_PROOF.md) now have a composed
execution theorem. We still need to connect the thrust bodies and side guard
to that path, proving that each establishes the
next block's input relation, including preservation of cached `onground`,
commands, pointers and tables. Animation/state calls and the prologue/epilogue
are also outside this result. `P_MovePlayer` is only part of a complete tic;
collision, friction and the other game systems require their own connections.

The semantics use total flat memory and data-object-relative operands. Physical
memory validity, DOS loader/segment correspondence, instruction fetch, faults,
interrupts, timing, and the Lean compiler/runtime remain outside these proofs.
No engine behavior was changed and no complete DOS playthrough was rerun for
this proof/tooling addition.
