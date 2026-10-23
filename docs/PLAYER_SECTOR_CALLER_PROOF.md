# Original secret-sector caller correspondence

`SectorCaller.dispatched_observation` proves the original sector lookup, CALL,
four PUSHes, floor check, switch, secret-case effects and RET agree with the
live `LevelSpecials.secret` helper. The result covers both floor outcomes for
an initially secret sector. It restores the caller's ESP and ECX, EDX, EBX,
EBP, ESI and EDI, and returns to the instruction following the actual CALL.

The saved registers and return address are now consequences of executing the
original instructions. There are no preinstalled stack words or assumed
saved-return conditions in this theorem's input contract.

## Scope and connection

The continuous execution starts at original code offset `0x333d0`, immediately
after `P_CalcHeight`, and ends at `0x333e5`. Its checked program contains:

| Region | What is executed |
| --- | --- |
| `0x333d0`–`0x333e0` | Sector lookup, halfword special test and handler argument setup |
| `0x333e0` | CALL to `0x2fb20`, pushing return address `0x333e5` |
| `0x2fb20`–`0x2fb24` | PUSH EBX, ECX, EDX and ESI |
| Existing handler regions | Floor test, unsigned switch and actual CS-relative table jump |
| Secret or off-floor epilogue | Optional secret writes, four POPs, and RET |

There are 31 executed instructions on the floor, and 23 off the floor. The
bounded interpreter uses 31 as its budget and fails on exhaustion. The
CALL-only theorem starts at `0x333e0` with budget 25.

`dispatch_prefix` checks the same original lookup bytes used by the earlier
[sector-dispatch proof](PLAYER_SECTOR_DISPATCH_PROOF.md), now at absolute code
offsets. `call_prefix` executes the CALL and prologue. `saved_words` establishes
the five stack contents; `lookup_preserved` carries the input fields through
those writes; `establishes_inputs` derives the existing handler contract.
`execution` then reuses the [handler-path proof](PLAYER_SECTOR_ENTRY_PROOF.md).
`dispatched_execution` joins the lookup to that execution without replacing
memory, registers, flags, or PC at any seam.

The full final modeled state is specified by `dispatched_execution`.
`dispatched_observation` projects the return PC, sector special, secret counter
and seven preserved registers and connects them to the live helper. EAX holds
the object pointer on return; it is not a preserved register. Stack memory
retains the values written by CALL/PUSH even after POP/RET restore ESP.

## Remaining initial assumptions

Before the lookup, EDX addresses the player. The input contract requires:

- the sector's special halfword is 9;
- body Z, the sector floor, and the secret counter encode the supplied Lean values;
- the counter's four bytes and sector special's two bytes are disjoint;
- all handler input word reads avoid the five stack word writes.

The last condition covers the pointer chain, body Z, sector floor, special and
counter. It also establishes that the later secret writes cannot corrupt the
saved stack. For simplicity the read protection covers a full word at the
special address, although the original reads only its low halfword.

`Inputs (argument s)` expresses these facts about the initial memory using
EDX as the player argument; `argument` is a register projection, not an assumed
intermediate execution result. The actual argument-setting instruction is
executed by `dispatch_prefix`.

Adjacent stack slots are proved disjoint even across 32-bit address wraparound.
Their contents before CALL can be arbitrary. The proof neither requires a
valid old return word nor assumes that old stack values match the registers.

## Executable certificate and validation

The extractor pins the same shareware DOOM 1.9 executable SHA-256:
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
It checks the 21-byte caller region at file offset `0x753e4`, plus the handler
entry, switch table, secret case and off-floor return used by the existing
certificate. It verifies all expected code-object relocations.

```sh
./scripts/verify-original-sector-caller
python3 -m unittest discover -s tests -p 'test_original_sector_caller.py'
python3 scripts/verify_original_sector_caller.py --cross-check
```

Both CALL-only and complete lookup-to-return observations are bound directly
to the extracted byte lists. All **13 audited declarations** use only
`propext`, `Classical.choice` and `Quot.sound`, with no proof holes or unchecked
native axioms.

**50,124 independent original-byte/native comparisons passed**, including
16,708 on-floor and 33,416 off-floor runs. They begin with arbitrary registers
and unprepared stack contents, execute the original bytes in Unicorn, and
compare the secret fields against compiled Lean. Checks cover the entire
dynamic memory page, all registers, instruction counts, the actual branch and
table path, the five ordered stack stores, optional secret writes, and the
CALL-generated return. Two code relocation bases and all four byte alignments
are exercised.

**18 focused tests passed**: five caller tests, seven handler-entry tests, and
six existing sector-dispatch tests. The new tests reject changed CALL targets,
wrong argument/save/restore registers, altered branches, missing RET, mutated
table words, missing input contracts and unexpected proof axioms. They also
check a wrapping stack and fuel exhaustion. The proof target and its 103 build
jobs completed successfully.

## Proof checklist after this step

- Complete: sector lookup to secret-handler return, including CALL/prologue.
- Complete: deriving saved words, return address and the handler input contract.
- Complete: [join to player preparation](PLAYER_SECTOR_JOINED_PROOF.md), using
  actual DOS code-object PCs and CALL return words throughout, and deriving
  the handler contract from initial-state memory separation.
- Open: other sector types, damage/RNG calls, scene-memory adapter obligations,
  reachable-state invariants, the remaining tic, rendering and whole-game parity.

The theorem remains conditional on the stated initial memory relations and the
limited x86 semantics. It does not prove the DOS loader, segmentation/faults,
exact final EFLAGS, interrupts, timing, or Lean compilation. The finite machine
comparisons are independent validation, not a universal proof of those layers.
No gameplay code or running comparison service was changed.
