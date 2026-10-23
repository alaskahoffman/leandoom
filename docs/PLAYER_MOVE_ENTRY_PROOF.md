# Composed player movement entry

The original turning block and forward-movement guard now have a **continuous
execution proof**. Given a related initial memory state and any input command,
the original DOS instructions store the same turned angle as Lean and choose the
same forward-thrust branch. All input assumptions are made before turning;
there is no fresh assumption about game state at the turning/guard boundary.

This proves the entry portion of `P_MovePlayer`, not the complete player update.
It stops immediately before forward thrust, or at the sideways guard when
forward thrust is skipped.

## Exact scope

The checked slice contains 48 contiguous bytes at code-object offset `0x33169`
(EXE file offset `0x7517d`) of DOOM 1.9:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

There are 17 decoded instructions, with early branching allowed. Exit offsets
relative to this slice are:

- `48`, original address `0x33199`: execute forward thrust.
- `120`, original address `0x331e1`: skip forward thrust and enter the side guard.

The second destination lies beyond the slice. The proof stops at that declared
exit; it does not execute or make a claim about absent intervening bytes.
The extractor checks contiguous file mapping, original bytes, and the cached
`onground` address relocation at slice byte 36.

`move_entry_matches_engine` proves both the exit and the entire final memory.
The memory result is the starting memory with two ordered writes: the angle
computed by `Motion.turn`, then the cached ground predicate used by movement.
`move_entry_final_angle` separately proves that the latter write preserves the
new angle.

`MoveEntryInputs` relates the initial angle, signed turn word, forward command
byte, height and floor height to the actual Lean inputs. It requires byte-range
separation so the angle write does not corrupt the player pointer, height,
floor, or command bytes, and the cached-ground write does not corrupt the angle.
These premises are explicit caller obligations, not facts yet proved about all
reachable game states.

The lower-level `original_move_entry` theorem does not require these separation
assumptions: it describes the literal ordered memory and branch effects even
for overlapping memory. The engine theorem derives the needed guard inputs from
entry assumptions using `turn_establishes_guard_inputs`.

## Reusable composition machinery

`Doom/Verification/X86Compose.lean` adds three generic theorems:

- `Prefix.run` connects an exact execution prefix to the remaining execution.
  A prefix carries the full machine state and must establish that no outer exit
  was reached early. An arbitrary replacement state cannot be inserted.
- `runProgram_shift` relocates a locally proved block's program counters and
  exits while keeping memory, registers and flags intact. It currently requires
  nonnegative relative branch offsets, avoiding the model's negative-PC
  failure boundary.
- `runProgram_extend` embeds a successful execution of a partial instruction
  listing into a larger listing that agrees at every defined entry.

The six turning instructions establish `turnEndCore`, including ECX's player
pointer and ESI's command pointer. The proof then reuses the existing guard
execution theorem at PC 17. Every instruction in the combined proposed listing
is checked against the byte decoder. This joins actual execution states, rather
than merely conjoining two separate block correctness statements.

## Validation

```sh
./scripts/verify-original-move-entry
python3 -m unittest discover -s tests -p 'test_original_move_entry.py'
```

Optional independent validation with Capstone and Unicorn installed:

```sh
python3 scripts/verify_original_move_entry.py --cross-check
```

The initial run passed **78,080 continuous x86 comparisons**. It includes all
65,536 signed turn encodings, all 256 forward-command bytes, signed-height
boundary pairs, randomized angles/registers/flags, and unaligned player/object
addresses. The harness checks the branch destination, angle, all eight general
registers, ZF/SF/OF, the dynamic memory page, cached ground, and both writes in
order. Expected angles come from compiled `Motion.turn`; branch expectations
come from the compiled isolated forward-movement probe.

Five new tests validate the certificate and extraction, reject altered command
pointers/turn shifts/branch targets, reject replacement states at a seam, and
exercise insufficient fuel, early exits, and the relocation theorem's backward
branch restriction. Existing turning and movement-guard regression tests also
pass. The inlined-thrust and interaction proofs still build.

The byte identity uses no axioms. Composed theorems use only `propext`,
`Classical.choice` and `Quot.sound`; the verifier rejects unchecked native
checker axioms, `sorryAx`, missing audits, and unexpected output.

## Next boundary

The [forward-thrust/side-guard region](PLAYER_FORWARD_SIDE_PROOF.md) now has a
continuous proof, including preservation of the side guard's live inputs. The
[joined proof](PLAYER_MOVE_JOIN_PROOF.md) now derives that entry relation and
composes both regions under one initial relation. Side thrust remains a separate
body proof, with taken and skipped paths still to compose. Animation
calls and the prologue/epilogue remain outside the result, as do collision and
the rest of a player tic.

The model still uses total flat memory, immutable code and data-object-relative
addresses. This does not verify DOS loading, segment translation, memory faults,
physical instruction fetch, interrupts, timing, or Lean compilation/runtime.
No game behavior changed and no complete gameplay replay was rerun for this
proof-only milestone.
