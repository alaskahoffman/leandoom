# Original player movement guards

`Doom/Proofs/OriginalMoveGuards.lean` proves the ground check and the two decisions
that select forward and sideways thrust inside the original DOS `P_MovePlayer`.
The direct byte-to-engine theorems quantify over every related input state and
all initial projected flags; they do not assume the branch taken in a recording.

This extends the straight-line block tooling with checked conditional control
flow. It does **not** yet prove the entire `P_MovePlayer` routine or a player tic.

## Exact claims

The forward slice contains 11 instructions at code-object offset `0x3317a`.
It loads player->mo->z and floorz, performs signed CMP/SETLE, loads the forward
command into DL, writes the full `onground` word, and tests command and ground.
Its two exits are:

- `0x33199`: enter the inlined forward-thrust body;
- `0x331e1`: skip it and begin the sideways guard.

`original_forward_guard` proves both the exact exit and the entire memory effect:
only a four-byte store to the data-relative `onground` cell, `0x2cf90`.
`forward_guard_engine_pc` connects that exit to the real engine's ground
predicate and nonzero forward command. Equality of height and floor counts as
on ground, including all signed 32-bit extrema and subtraction-overflow cases.

The sideways slice contains five instructions at `0x331e1`. It loads DH from the
side command and reads the **cached** `onground` word; it does not recompute the
height comparison. Its exits are:

- `0x331f1`: enter the inlined sideways-thrust body;
- `0x3323e`: skip it and reach the animation-selection logic.

`original_side_guard` proves the exit and that all memory is unchanged. Its raw
claim handles any cached 32-bit ground word, not just zero and one.
`side_guard_engine_pc` adds the explicit relation between that cached word and
the engine's ground predicate.

`Motion.onGround` factors out the existing height comparison used by
`Motion.movePlayer`; this is the only engine refactor. The predicate is
definitionally the previous comparison. Turning and thrust are separately proved
to preserve it. These facts help future composition; they do not prove the
original inlined blocks preserve every caller invariant.

## Reusable control-flow layer

`Doom/Verification/X86Control.lean` uses the same byte-addressed memory and
straight-line operations as `X86Block`. It adds the forms required by these
slices: memory comparisons, SETLE, byte loads, TEST, AND, a global store, and short
JE/JNE branches. The byte-register model distinguishes AL/CL/DL/BL from
AH/CH/DH/BH and preserves neighboring bits on writes.

The flag projection includes ZF, SF and OF. CMP derives them from wrapping
subtraction. `cmp32_signed_le` proves that `ZF || (SF != OF)` is the signed
less-or-equal predicate for every pair of 32-bit operands. This is a kernel proof
using bitvector lemmas and integer arithmetic, not a native SAT-certificate
checker assumption.

MOV-like operations preserve flags. Operations for which the layer has no flag
semantics invalidate the flag projection. A conditional consumer of unknown
flags fails. This deliberately prevents composition from borrowing stale flags.
Zero-count shifts preserve flags; other unmodeled shifts invalidate them.

`runProgram_sound` lets us propose a sparse decoded control-flow listing and
prove it against the byte decoder. Each listed instruction must match. A
successful execution of the listing then agrees with byte execution. Fuel
exhaustion, missing instructions and unsupported encodings are failures; only
explicitly designated exits are successful. For these two acyclic slices the
universal proofs establish success within 11 and 5 instructions respectively.
These are sufficient execution bounds, not bounds on the input values.

The original compiler **inlined** both thrust computations in `P_MovePlayer`.
We cannot simply substitute the earlier standalone `P_Thrust` theorem at those
addresses. Connecting the inlined blocks with the new guards is the next step;
the fixed-multiplication summaries can still be reused inside them.

## Reproduce

With the hash-pinned shareware archive installed:

```sh
./scripts/verify-original-move-guards
```

The script verifies the executable hash, LE file mapping, exact slices and their
`onground` data relocations. It generates a Lean certificate from the extracted
bytes and rejects any unexpected proof axioms. Output is in
`artifacts/original-move-guards/`.

Optional independent Capstone/Unicorn comparison:

```sh
/private/tmp/leandoom-binary-tools/bin/python scripts/verify_original_move_guards.py --cross-check
```

The initial run passed **34,336 cases**: 22,544 forward and 11,792 sideways.
It covers all 256 command bytes, signed-height extrema, seeded random values,
noncanonical cached ground words and unaligned player/object pointers. It checks
branch exits, all eight general registers, ZF/SF/OF, memory-write addresses and
the cached ground value. Comparisons with the compiled `Motion.movePlayer` use
isolated forward/side commands at angle zero and observe whether momentum was
added. The tests support the universal theorem; they do not replace it.

Four regression tests verify certificate auditing, reject modified comparisons
and branch destinations, check flags/byte registers and failure boundaries, and
validate extraction. The existing 89 fidelity tests also pass. Related movement,
turning, thrust and interaction proofs build successfully.

The audited byte identities use no axioms. The main execution/engine claims use
only `propext`, `Classical.choice` and `Quot.sound`. Early development exposed
native-checker dependencies in several bitvector proofs; these were replaced
before the final certificate was accepted. Native-checker axioms remain rejected
by the verifier.

## Remaining boundaries

The model has total flat memory, immutable code bytes and code-relative PCs.
It does not establish physical access validity, instruction-fetch behavior,
self-modifying code, interrupts, segment/loader relocation correspondence,
physical timing, or the Lean compiler/runtime. Negative relative targets are
rejected rather than treated as wrapping physical addresses; these guard slices
only use forward branches.

The [composed entry proof](PLAYER_MOVE_ENTRY_PROOF.md) now establishes the first
guard's input relation from preceding turning execution. The side guard's entry
relation still needs to follow from the full preceding path. The [inlined forward and sideways bodies](PLAYER_INLINE_THRUST_PROOF.md)
now have separate proofs. The complete proof still needs their composition,
preservation of the cached ground and pointer/table invariants,
animation calls, and the stack/return wrapper.
No whole-game equivalence or additional complete DOS playthrough is claimed here.
