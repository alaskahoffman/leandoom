# Original secret-sector case correspondence

`SectorSecret.observation` proves that the original DOS secret-discovery case
produces the same secret count and sector special as the live
`LevelSpecials.secret` helper, under explicit case-entry premises. It includes
the two writes, four POPs and actual RET: seven original instructions.

This is a component of `P_PlayerInSpecialSector`. It starts at its case-9 body,
not at the handler's entry. The previous [sector-dispatch proof](PLAYER_SECTOR_DISPATCH_PROOF.md)
still stops before the outer CALL. The [handler-path proof](PLAYER_SECTOR_ENTRY_PROOF.md) now connects the floor
equality check and actual switch dispatch to this component, starting just
after the four PUSHes. The [caller proof](PLAYER_SECTOR_CALLER_PROOF.md) now
adds those PUSHes and the outer CALL, deriving the saved stack words. The
[continuous joined proof](PLAYER_SECTOR_JOINED_PROOF.md) connects that caller
segment to preparation using only initial-state contracts.

## Result and original bytes

The extractor pins 17 bytes at code offset `0x2fbdc`, file offset `0x71bf0`,
in shareware DOOM 1.9. This region has no relocation entries. The standalone component uses local PC
zero at that address. The handler/caller/joined proofs lift it to absolute
code-object offsets and derive the outer CALL return word.

| Instruction | Effect |
| --- | --- |
| `INC dword [ESI+0xd4]` | Increment the player's signed 32-bit secret counter with wraparound |
| `MOV word [ECX+0xe], 0` | Clear exactly the sector's two-byte special field |
| `POP ESI`, `POP EDX`, `POP ECX`, `POP EBX` | Restore four values from the saved stack |
| `RET` | Read the saved return address and advance ESP |

`execution` gives the exact final register and memory state. EAX, EBP and EDI
are unchanged. The four popped registers equal their original stack words;
the proof does not assume those words already correspond to an earlier caller's
registers. ESP advances by 20 bytes. The return PC equals the original fifth
stack word, not an independently supplied replacement address.

`observation` connects the count and special field directly to the existing
`LevelSpecials.secret` function used by the runtime. Its premises say:

- the player is on the sector floor;
- the initial sector special word is 9;
- the original counter encodes the supplied Lean `Int32` count;
- the four counter bytes do not overlap the two sector-field bytes;
- the five stack words do not overlap either write;
- the return PC lies outside this 17-byte component's local code range.

The original INC wraps, including `2147483647 → -2147483648` and `-1 → 0`,
matching Lean's `Int32` operation. Clearing the special field is the state
change that lets the higher-level dispatcher avoid counting it again; the
whole-game once-only property still needs that dispatcher connected.

## Exact memory preservation

`updated_frame` is a byte-level result: every byte outside the four counter
bytes and two special-field bytes is unchanged. In particular, the two bytes
immediately after the sector special remain untouched. Address arithmetic is
32-bit and wrapping; unaligned reads and writes remain explicit.

`StackSafe` uses this exact footprint. `saved`, `updated_return` and
`updated_restored` derive the saved-word and return preservation from it. The
counter/sector separation premise is required for the live-field relation,
while the execution theorem itself models the writes in order even if those
two fields overlap.

The x86 decoder now supports the specific memory forms of `FF /0` (INC) and
`66 C7 /0 iw` (16-bit immediate store). Unsupported operand forms and truncated
encodings fail closed. INC's flag projection is invalidated: its exact flags
are not proved, and none of the remaining instructions consumes flags.

## Validation

```sh
./scripts/verify-original-sector-secret
python3 -m unittest discover -s tests -p 'test_original_sector_secret.py'
python3 scripts/verify_original_sector_secret.py --cross-check
```

The generated certificate binds the execution and live-helper observation
directly to the extracted original bytes. Its nine audited declarations allow
only `propext`, `Classical.choice` and `Quot.sound`, with no proof holes or
unchecked native axioms.

The independent comparison runs those bytes in Unicorn and compares against
compiled `LevelSpecials.secret` through the existing `level-probe`. **16,708
cases passed**, covering signed counter boundaries, random counts and floor
values, all four byte alignments, arbitrary saved registers and varying return
addresses. Checks include the entire dynamic memory page, the ordered 4-byte
then 2-byte writes, all registers and the stack-supplied return.

The formal proof is universal under its premises; the independent comparisons
are finite checks of the model and compiled implementation. Neither proves the
handler entry conditions, damage branches, outer CALL/RET composition, scene
adapter, compiler or whole-game equivalence. No game behavior was changed.


Regression validation passed all seven new secret-case tests, the six existing
sector-dispatch tests, and the 24 existing height/preparation tests. The new
tests check instruction mutations, missing entry/stack premises, precise store
widths, wrapping addresses, signed counter limits and decoder rejection. All
existing preparation and dispatch proof modules were rebuilt after extending
the instruction decoder.
