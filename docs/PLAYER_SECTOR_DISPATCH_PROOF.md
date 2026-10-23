# Original player-sector dispatch correspondence

**Follow-on:** [the continuous secret-sector proof](PLAYER_SECTOR_JOINED_PROOF.md)
now joins preparation through the actual handler return. Preparation and dispatch
PCs use absolute DOS code-object offsets. Standalone height components retain
their explicitly described local coordinate system.

`SectorDispatch.joined_execution` extends the continuous preparation proof
through the sector decision immediately after `P_CalcHeight`. It runs the
original reaction, movement, walking-state and height bytes, then follows the
player → object → subsector → sector pointer chain and tests the sector's
16-bit special field.

The result is conditional on the existing preparation input contract plus
protection of the initial sector lookup data from preparation writes. It does
not assume a new intermediate state or the result of the sector check.

## What is proved

Using absolute DOS code-object offsets, one execution starts at `0x333b1`
and ends at one of two boundaries:

| Sector special word | PC | Meaning |
| --- | --- | --- |
| Zero | `0x333e5` | Skip special-sector handling |
| Nonzero | `0x333e0` | Immediately before its CALL, with EAX equal to the player pointer |

The bound is 231 instructions: the existing preparation bound of 225 plus
six dispatch instructions. The actual run may be shorter. All 65,535 nonzero
16-bit patterns take the special path; it is not a positive-number test.

At either boundary, all eleven proved preparation fields still hold. Caller
ESP and the player pointer in EDX are preserved. The memory frame still relates
the final memory to the original entry memory, outside preparation's combined
write footprint: the dispatch itself performs no writes.

The proof chain is:

1. `PlayerPreparation.reaction_player` proves EDX survives either reaction path,
   using the existing movement function's register-restoration theorem.
2. `PlayerPreparation.execution_preserved` carries EDX through the height call.
   The earlier `execution` theorem remains available as a projection.
3. `SectorDispatch.special_preserved` carries the initial pointer chain and
   sector word through preparation using the combined memory frame.
4. `SectorDispatch.execution` proves the new original-byte region for arbitrary
   flat memory and registers, including both branch outcomes.
5. `SectorDispatch.joined_execution` composes both phases without resetting any
   register, memory, flags or PC. `observation` exports the branch destination,
   eleven preparation fields, ESP and EDX.

The live `Player.prepareTick` connection for those eleven fields continues to
be supplied by `PreparedRuntime.correspondence`. This new result establishes the
DOS control-flow boundary for the next proof; it does not yet prove the live
sector-effects adapter equivalent to the DOS handler.

## Initial read protection

`SectorDispatch.Safe s` requires that the following initial addresses are
separate from the combined preparation write footprint:

- the player-to-object pointer at EDX;
- the object's subsector pointer at offset 52;
- the subsector's sector pointer at offset zero;
- the sector special at offset 14.

The existing frame uses four-byte reads, so protection of the last field is
conservatively stated for four bytes. The branch nevertheless reads only two:
`load_half` proves it equals the low half of that framed word. Dirty bytes after
the field cannot affect the branch. Addresses remain byte-addressed, unaligned
and wrapping as in the existing flat-memory model.

This is an explicit additional initial-state premise. Establishing it from the
actual DOS allocation layout and reachable game states remains an obligation.

## Decoder and executable binding

The new instruction is `66 83 /7 ib`: a memory CMP with a 16-bit operand and a
sign-extended 8-bit immediate. Its subtraction, ZF, SF and OF are computed at
16 bits. The later handler-path proof also supports the register form and models its
unsigned carry flag for JA. Other unsupported opcode extensions and truncated
instructions fail closed.

The extractor checks 21 original bytes at code offset `0x333d0`, file offset
`0x753e4`, with no relocation entries. These include the following CALL's
encoding, although the theorem stops before executing it. The five previous
regions are also re-extracted and checked. The generated `joined_checked`
certificate directly names all six extracted byte lists.

```sh
./scripts/verify-original-sector-dispatch
python3 -m unittest discover -s tests -p 'test_original_sector_dispatch.py'
python3 scripts/verify_original_sector_dispatch.py --cross-check
```

## Boundary and next work

The nonzero branch stops **before** `P_PlayerInSpecialSector` is called. No
handler result, damage, RNG change, secret discovery or return is assumed.
Ordinary-sector execution stops before command-button processing. The [secret-discovery case](PLAYER_SECTOR_SECRET_PROOF.md) now has a separate
original-byte proof through its RET. The [handler-path proof](PLAYER_SECTOR_ENTRY_PROOF.md)
now joins its floor guard and switch dispatch to that case, starting after the
handler PUSHes. The [caller proof](PLAYER_SECTOR_CALLER_PROOF.md) now also executes
the lookup, CALL and PUSHes through the handler RET. The
[joined proof](PLAYER_SECTOR_JOINED_PROOF.md) connects it to preparation for
initially secret sectors. Damage paths remain open.

This remains a universal conditional theorem in the project's limited flat x86
model. It does not establish DOS loading, memory-fault behavior, compiler
correctness, initialization, reachable-state invariants, rendering or whole-tic
and whole-game equivalence.

## Validation

- Lean built the composed proof and the original-byte certificate; all **47
  audited declarations** use only the existing allowed axioms (`propext`,
  `Classical.choice`, `Quot.sound`), with no proof holes or unchecked native axioms.
- **30 regression tests passed**: six new dispatch tests and the 24 existing
  height/preparation tests. They cover byte mutations, wrong branch claims,
  missing read protection, halfword width, wrapping loads, signed overflow,
  sign-extension and unsupported encodings.
- **65,536 independent Unicorn runs passed**, one per 16-bit sector value,
  checking the branch, argument, other registers, modeled flags and unchanged
  memory, with dirty adjacent bytes and unaligned addresses.
- **52,052 continuous original-byte comparisons passed** through preparation
  and dispatch, retaining the compiled Lean preparation-field comparison,
  full dynamic memory page, stack contents, return words and write checks.
  These runs use two data relocation bases. The special-sector handler is
  excluded from both the formal result and these comparisons.

Only proof, verification and documentation code changed. Game behavior and the
running comparison services were not changed.
