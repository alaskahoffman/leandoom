# Joined movement correspondence from one initial state

The previously separate turning/forward-guard and forward-thrust/side-guard
regions are now joined into **one uninterrupted original-byte execution proof**.
All data and memory-layout assumptions are made before turning. No new input
relation is assumed at either intermediate boundary.

For any related starting state, signed 16-bit turn command and signed 8-bit
forward/side commands, the proof covers:

1. Turning with the original 32-bit angle wraparound.
2. The signed ground check and cached `onground` write.
3. Choosing whether to execute forward thrust.
4. Forward momentum computation and its scratch write when selected.
5. The sideways-thrust decision using the preserved side command and cache.

Execution stops before sideways thrust, or at the animation-selection code when
sideways thrust is skipped. Side thrust, animation, collision and the rest of a
player tic remain outside this theorem.

## Bytes and statements

The certificate binds 136 contiguous bytes, starting at code-object offset
`0x33169` / file offset `0x7517d`, from the shareware DOOM 1.9 executable:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

All four LE data-operand relocations are checked. The region contains 45 decoded
instructions; a branch can skip some of them. The proof uses a sufficient fuel
bound, not an assertion that each path executes 45 instructions.

| Exit relative to region | Original address | Meaning |
| --- | --- | --- |
| 136 | `0x331f1` | Start sideways thrust |
| 213 | `0x3323e` | Skip sideways thrust; enter animation selection |

The second exit lies beyond the byte slice. It is a declared stopping point,
not a claim about instructions beyond the slice.

`move_join_matches_engine` proves the final branch destination and entire
memory result, including the original ordered stores. The result consists of
the angle and cached-ground stores, followed by the scratch/momentum stores
only when forward thrust is taken.

`move_join_observation` separately projects the final angle, momx and momy.
`move_join_player_observation` connects those fields directly to the actual
`Motion.movePlayer` function with side input set to zero. An intermediate lemma
proves that this projection equals turning followed by conditional forward
thrust, including both animation-frame branches. The scratch and momentum
writes are required to be disjoint from the angle so that this final angle
claim follows from the memory theorem.

## One initial relation

`MoveJoinInputs` relates initial angle, command bytes, height, floor and momenta
to the Lean inputs and requires the existing sine-table invariant. Its layout
conditions keep the entry stores, scratch word, momentum fields, cached ground,
player pointer and live command bytes from corrupting subsequent reads.
Protection of the complete table allows the turned angle to select any entry;
there is no assumption about which lookup will occur after turning.

The important connecting theorem is `entry_establishes_forward_side`. It
**derives** the downstream `ForwardSideInputs` relation from `MoveJoinInputs`.
In particular, the derived command, updated angle, unchanged momenta, preserved
tables and newly written cached ground all come from the actual entry execution.
The caller does not supply a fresh state or relation at the seam.

This is still conditional on the initial relation. A verified loader and proof
that every reachable caller state establishes that relation remain future work.
The assumptions concern initial data and separation; they do not assume the
result or equivalence being proved.

## Composition details

The forward-guard theorem was strengthened to retain its entire core and flag
state. `move_entry_full` now identifies the complete state at either entry exit.

`Doom/Verification/X86Paths.lean` supplies reusable path machinery:

- Extract the executed prefix and actual instruction count from a successful
  bounded run, including early exits.
- Transfer that prefix into a larger program only when all executed
  instructions agree and none is a final exit of the enclosing region.
- Finish execution from exactly the prefix's output state.
- Increase a sufficient fuel bound without executing beyond a declared exit.

The combined listing and shifted suffix are checked against the byte decoder.
The proof handles taken and skipped forward branches separately, then combines
them into the universal initial-state theorem.

## Validation

```sh
./scripts/verify-original-move-join
python3 -m unittest discover -s tests -p 'test_original_move_join.py'
```

With the optional Capstone and Unicorn packages:

```sh
python3 scripts/verify_original_move_join.py --cross-check
```

The initial independent run passed **132,352 continuous x86 comparisons**:

- All 65,536 turn encodings with varied signed heights, angles and commands.
- All 65,536 forward/side command pairs while grounded.
- 1,280 additional airborne cases covering every side command and selected
  forward extremes, including zero.

The harness varies full-width momenta, initial registers/flags, unaligned
player/object/scratch addresses and two data relocation bases. It checks the
whole region without resetting state at either seam: final angle, momentum,
branch destination, all eight general registers, ZF/SF/OF, cached ground, the
dynamic memory page and write order.

The `move-front` probe calls the real compiled `Motion.movePlayer` with side
input suppressed to observe angle/forward momentum. A separate isolated side
update supplies the expected side-branch observation. This comparison stops at
the same logical boundary as the theorem; it does not compare side-thrust
results yet. The original sine table is also checked against all 10,240 compiled
Lean entries.

The certificate audits both memory and observable-field claims. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted; unchecked native checker
axioms and `sorryAx` are rejected. Tests reject altered bytes, missing
relocations, shortened paths, premature exits and malformed audits, and check
that the downstream relation is obtained from the initial relation alone. The
final validation passed 105 targeted tests: six new joined-proof tests, ten
existing region tests, and 89 fidelity regressions. The interaction proof still
builds.

## Remaining scope

The [complete motion proof](PLAYER_MOVE_MOTION_PROOF.md) now carries the
complete side-guard output into the side-thrust body, retaining the skipped-side
path and deriving its inputs from the initial relation. Animation/state calls
and the prologue/epilogue remain next. Even all of `P_MovePlayer` would still be only part of
a complete tic, not whole-game equivalence.

The semantics use total flat memory, immutable code and data-object-relative
addresses. DOS loading/segmentation, memory faults, physical instruction fetch,
interrupts, timing and Lean compilation/runtime remain outside these proofs.
Only proof/tooling and a diagnostic probe changed; no game behavior changed and
no complete gameplay replay was rerun for this milestone.
