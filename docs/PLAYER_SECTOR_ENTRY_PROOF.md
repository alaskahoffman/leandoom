# Original secret-sector floor check and switch correspondence

**Follow-on:** [the continuous secret-sector proof](PLAYER_SECTOR_JOINED_PROOF.md)
now joins preparation through the actual handler return. Preparation and dispatch
PCs use absolute DOS code-object offsets; any relative coordinates below describe
the earlier component proof and have since been migrated.

`SectorEntry.observation` connects the original DOS handler's floor check and
compiler-generated switch to the secret-case writes, saved-register restoration
and RET. The result matches the live `LevelSpecials.secret` helper for either
floor outcome. The player must be exactly on the sector floor to discover the
secret; both higher and lower Z values leave the count and sector unchanged.

This is a universal conditional proof about original bytes in our limited x86
model. It starts at `0x2fb24`, immediately **after** four PUSH instructions. It
does not itself connect the outer CALL or derive the saved stack words. The
[caller proof](PLAYER_SECTOR_CALLER_PROOF.md) now supplies that connection.
Other sector types, including damage, remain open.

## Continuous execution

The theorem follows one machine state throughout these operations:

1. Read player → object → subsector → sector, and compare the object's Z with
   the sector's floor height.
2. Off the floor, branch directly to the ordinary POP/RET epilogue.
3. On the floor, load the 16-bit sector special into DX, subtract four, compare
   the low halfword with twelve, and execute the unsigned JA range check.
4. Mask the index to 16 bits and jump through the original CS-relative table.
   Sector 9 selects entry 5, whose target is the original case at `0x2fbdc`.
5. Execute the previously proved counter increment and two-byte sector clear,
   then restore four registers and use the saved return address.

The run uses a budget of 20 instructions: 20 on the floor, 12 off it. A budget
exhaustion is a failure, never a successful exit. `floor_prefix`, `switch_run`,
`select`, `secret_tail` and `execution` compose checked paths; there is no new
assumed intermediate machine state at their boundaries.

`execution` specifies the complete modeled final state. `fields` connects its
memory to the live helper. `observation` combines that result with the actual
return PC and ESP advancement. The existing secret-case memory-frame theorem
still describes exactly which bytes change. On the off-floor branch, no data
bytes change. Signed counter increment wraps exactly as before.

## Initial contracts and model boundary

The inputs require the initial sector special to be 9; the original Z, sector
floor and counter to encode the supplied Lean values; the counter and special
fields to be disjoint; the five saved stack words to avoid those writes; and
the saved return address to lie beyond the modeled handler regions.

There is no assumption that the floor comparison succeeds or that the switch
already selected case 9. Those are derived by executing the entry bytes.
Addresses and counter arithmetic wrap at 32 bits, and loads may be unaligned.
Establishing these contracts from actual reachable game states remains separate.

`X86CodeMemory` adds immutable code-segment memory for the table read. It reuses
the existing instruction semantics for all other operations. This matters
because the original jump has a CS override: reading the table from player/data
memory would model a different instruction. This is still a projection, not a
complete model of DOS loading, segmentation faults, physical instruction fetch,
interrupts or timing. The formal code addresses use an unrelocated code origin.

The decoder supports the required halfword register load/compare, near JNE,
JA, register AND and CS-relative indirect jump. Carry is explicitly known for
the new unsigned comparison; JA fails closed when carry is unknown. Existing
instructions that do not model carry retain an unknown value. The secret INC
continues to invalidate flags because exact final EFLAGS are outside the claim.

## Executable binding and validation

The extractor pins shareware DOOM 1.9 SHA-256
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.

| Region | Code offset | Bytes |
| --- | --- | --- |
| Handler prologue and entry dispatch | `0x2fb20` | 55 |
| Original 13-entry switch table | `0x2faec` | 52 |
| Secret case and its return | `0x2fbdc` | 17 |
| Off-floor return | `0x2fc39` | 5 |

The four prologue bytes are bound to the executable but not executed by this
theorem. All code-object relocations in the table and jump operand are checked
against the executable's fixup records. Code relocations require explicit
extractor permission; existing data-only extraction retains its old default.

```sh
./scripts/verify-original-sector-entry
python3 -m unittest discover -s tests -p 'test_original_sector_entry.py'
python3 scripts/verify_original_sector_entry.py --cross-check
```

The generated certificate directly names the four extracted byte lists and
proves the live-helper observation. All **11 audited declarations** use only
`propext`, `Classical.choice` and `Quot.sound`. The partial-register identity
uses kernel-checked bit-width lemmas, with no unchecked native proof axioms.

**50,124 independent original-byte/native comparisons passed**: 16,708 on-floor
and 33,416 off-floor runs. They compare against compiled Lean through
`level-probe`, covering signed limits, wrapping counter values, random data,
all four byte alignments and two code relocation bases. Checks include the
entire dynamic memory page, ordered write addresses and widths, all registers,
the table/branch path, ESP and the stack-supplied RET.

Seven new tests cover the certificate, strict axiom audit, byte/table mutations,
missing initial contracts, unsigned flags, code/data separation and relocation
permissions. The existing guard, movement-entry, height, sector-dispatch and
secret-case suites also passed: **53 focused tests in total**.

These finite comparisons check the model and compiled helper independently;
they do not turn the conditional proof into whole-game equivalence. The
[caller proof](PLAYER_SECTOR_CALLER_PROOF.md) now executes the lookup, actual
outer CALL and four PUSHes and derives this component's stack and input contracts.
The [continuous joined proof](PLAYER_SECTOR_JOINED_PROOF.md) now connects that
segment to player preparation. No game behavior or running comparison service
was changed.
