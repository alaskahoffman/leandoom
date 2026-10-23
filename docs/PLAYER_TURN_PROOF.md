# Original player-turn block

`Doom/Proofs/OriginalTurn.lean` proves the original shareware DOOM 1.9 angle-update
block agrees with the engine's `Motion.turn`. `Motion.movePlayer` calls this same
helper before thrust; extracting the helper preserves its former expression.

This is a local original-binary-to-engine theorem. It does not establish
thrust, collision, complete player updates, or whole-game pixel correspondence.

## Original bytes and correspondence

The six-instruction block starts at code-object offset `0x33169`, file offset
`0x7517d`, immediately after the `P_MovePlayer` prologue:

```asm
mov   ecx, eax
lea   esi, [eax + 8]
movsx ebx, word ptr [esi + 2]
mov   eax, dword ptr [eax]
shl   ebx, 16
add   dword ptr [eax + 32], ebx
```

At this entry EAX contains the player pointer. The player begins with a pointer
to its map object; the turn command occupies two bytes at player+10; the map
object's angle occupies four bytes at mobj+32. `player_turn_matches_doom19`
explicitly assumes the command and angle in that memory agree with the supplied
Lean `Int16` and `Motion` values. It then proves that the final angle field equals
the actual engine's updated angle, over all such input states.

The theorem includes all 65,536 signed command values and all 2^32 starting
angles, not only the demo format's coarser turn commands. It preserves negative
turns and modulo-2^32 angle arithmetic. Initial values of the other registers
and memory are unrestricted within the model.

## Semantics and proof

`Doom/Verification/X86Memory.lean` adds a small straight-line register/memory
projection alongside the existing arithmetic models. It decodes register MOV,
selected non-SIB memory operands, LEA, MOVSX from a word, immediate SHL, and
ADD into memory. Unsupported encodings, prefixes, missing operands, extra bytes,
or incorrect instruction counts fail instead of being silently skipped.

Memory maps 32-bit addresses to bytes. Little-endian loads and stores preserve
overlap and unaligned accesses. No assumption that differently named fields
occupy separate abstract memories is made. Effective-address arithmetic wraps.

The kernel-checked results are:

- `original_turn_memory`: decoding and executing the actual 17 bytes gives the
  specified memory update, for any initial modeled registers and memory.
- `player_turn_matches_doom19`: the stored angle is exactly `Motion.turn`'s angle
  when the stated input fields correspond.
- `player_turn_preserves_other_bytes`: every byte outside the four angle bytes
  is unchanged.
- `player_turn_preserves_register`: EDX, ESP, EBP and EDI are unchanged.

The load/store lemma uses Lean's proof-producing `bv_decide`; the arithmetic
identity and execution summary use kernel-checked rewriting. No `sorry`, added
axioms or native-evaluation shortcuts are used. The extracted angle/footprint
theorems' axiom audit contains only `propext` and `Quot.sound`; the extracted-byte
identity uses no axioms.

## Reproduce and validate

After fetching the existing pinned shareware archive:

```sh
./scripts/verify-original-turn
```

The script checks the archive and executable hashes through the existing
extractor, verifies LE code mapping and absence of overlapping relocations, and
generates `artifacts/original-turn/Extracted.lean` from the actual executable
slice. Lean proves the extracted-byte identity and angle theorem. An axiom audit
must pass before the report is written. The normal test suite builds this proof
and checks that altered shift counts and write addresses fail their certificates.

Optional independent tests, using the same Capstone/Unicorn environment as the
arithmetic verifier:

```sh
/tmp/leandoom-binary-tools/bin/python scripts/verify_original_turn.py --cross-check
```

The initial run passed 65,571 cases, including every signed command, angle
extrema, seeded angle inputs, and unaligned player/object pointers. It compares
the original bytes' result with the compiled Lean helper and checks all general
registers and all 4 KiB of mapped data for unexpected writes. These are supporting
tests; the universal theorem does not depend on the emulator.

## Explicit boundary

This model assumes a valid block entry, 32-bit operand/address mode and accessible
flat data memory, with no external interference. It projects away EFLAGS,
instruction fetch, access faults, segmentation, interrupts, physical timing,
and the routine's prologue/epilogue. The following original CMP establishes new
flags before conditional use; this proof cannot justify arbitrary callers that
observe the omitted flags. Abstract wrapping memory accesses do not establish
that corresponding physical accesses would succeed.

Executable identity, ZIP extraction, loader mapping, correspondence of our ISA
model to physical x86, and the Lean compiler/runtime remain outside the kernel
theorem, as in the existing arithmetic proofs. The file offsets and the field
relation identify the block but are not a proof that the whole game's control
flow reaches it with corresponding state. That caller invariant, then thrust
and collision correspondence, are subsequent obligations.
