# Original dead-player weapon lowering

`Doom.Proofs.OriginalWeaponLower` proves the original DOS `A_Lower` action for a
dead player, from `0x2d490` through its RET to `0x2d095` in `P_SetPsprite`.
For every 32-bit input height satisfying the memory contract, the final weapon
height equals the live Lean engine's `Weapon.lowerHeight y true`.

This action theorem is now reused by the [complete weapon-drop call-chain
proof](WEAPON_DROP_PROOF.md), including the weapon-table lookup, psprite setter,
indirect action CALL and returns. That continuation is also joined to the
continuous lethal-damage proof. The rest of the death sequence remains open.

## What the original instruction does

The first movement instruction is `add word ptr [edx+14], 6`. The psprite's
32-bit y field starts at offset 12, so this updates only its upper 16 bits.
The proof establishes that the result is exactly addition of `6 * 65536` to the
entire fixed-point word, modulo 2^32, while preserving its fractional bits.
It checks the actual two-byte memory write, not a replacement four-byte store.

The original then compares the wrapped result as a signed integer against
`128 * 65536`. A dead player is clamped to 128 only when that comparison reaches
the bottom. For example, a very large positive input can wrap negative during
the addition and therefore take the below-bottom branch. The theorem includes
that case rather than assuming screen-sized heights.

## Formal boundary and live code

`Inputs` relates the initial y word to `Fixed.raw`, requires player state 1
(dead), and requires the actual callback return address on the stack. Its
indexed separation predicate keeps the player-state word, y word, saved EBX
slot and return-address slot disjoint. No aligned-address premise is needed.

The theorem proves:

- the decoded original program reaches the setter's continuation in at most
  nine instructions;
- its y word equals the live `Weapon.lowerHeight` result;
- every register is restored except ESP, which advances by four on RET;
- memory outside the y word and saved-register slot is unchanged.

`Weapon.lowerHeight` is a total function extracted from the existing live
`A_Lower` branch. That branch now calls the helper while retaining the existing
alive-player switching/removal behavior. The machine correspondence theorem
is about the dead-player height operation; it does not prove the private partial
`Weapon.enter` dispatcher or arbitrary psprite state chains.

The decoder adds the specific memory ADD16-with-sign-extended-immediate form.
Its memory update is explicit and byte-addressed. The model discards that
instruction's arithmetic flags, which the immediately following CMP overwrites.
This remains the project's limited flat x86 semantics, not a complete processor,
loader or compiled-Lean correctness theorem.

## Reproduction and evidence

```sh
./scripts/verify-original-weapon-lower
# With Unicorn and local JIT access:
python3 scripts/verify_original_weapon_lower.py --cross-check
python3 -m unittest discover -s tests -p test_original_weapon_lower.py -v
```

The certificate binds the 60-byte original action region to the pinned
DOOM.EXE, checking file placement and relocations. Thirteen declarations pass
the strict axiom audit: only `propext`, `Quot.sound` and `Classical.choice`.
The bit-vector arithmetic and memory lemmas use kernel-checked proofs rather
than native evaluation axioms.

Independent emulator checks cover 67,614 heights: every one of the 65,536 high
halves with varied fractional bits, explicit signed/clamp edges, and random
words. Expected heights come from full compiled Lean `Weapon.drop` calls for
fists, pistol and shotgun. The comparison checks all registers, exact ordered
writes, surrounding memory, unaligned fields, a wrapping stack, and a height
field near the top of the 32-bit address space. There are 33,955 below-bottom
cases and 33,659 clamped cases.

Lean execution fixtures additionally check wrapping field addresses and stacks.
Decoder tests exercise all 256 signed immediate bytes and reject truncated and
unsupported encodings. Negative certificates reject changed increment widths,
amounts, comparisons, branches and return bytes, missing contracts, the wrong
live dead flag, and an incorrect stack result.

The existing weapon oracle still matches 68,480 commands against original C at
both `-O0` and `-O2`, covering raising, switching, firing and death lowering.
All five new proof/decoder tests, five preceding kill-bookkeeping tests, ten
weapon regressions and eleven death regressions pass (31 total), after rebuilding
the game and relevant probes. The earlier corpse proof needed a larger local
simplifier step budget after the decoder extension; its statement is unchanged.
These tests support the implementation and model; the universal claim comes
from the theorem under its stated premises.
