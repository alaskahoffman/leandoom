# Original player angle and momentum correspondence

The motion region of the shareware DOS DOOM 1.9 `P_MovePlayer` now has one
continuous, kernel-checked correspondence proof, from turning through both
conditional thrusts. For every initial state satisfying `MoveMotionInputs` and
**every signed 16-bit turn and signed 8-bit forward/side command**, execution
reaches the animation-selection entry with exactly the angle, momx and momy
produced by the actual Lean `Motion.movePlayer cmd` function. Neither command
is suppressed in this statement.

This is a universal local theorem, not whole-game equivalence. It does not yet
prove that every reachable caller state satisfies the initial relation.

## What is connected

`Doom/Proofs/OriginalMoveMotion.lean` connects these operations without resetting
registers, memory or flags at the boundaries:

1. Turn with 32-bit wraparound.
2. Compare signed height and floor, and store the cached ground flag.
3. Take or skip forward thrust.
4. Load the sideways command into DH and take or skip side thrust.
5. Apply the quarter-turn angle offset and update both momenta for side thrust.
6. Reach code-object address `0x3323e`, immediately before animation selection.

`move_motion_matches_engine` describes the entire final memory, including the
angle, cached-ground and temporary stack stores. The thrust stores remain in
forward-then-side order. `move_motion_player_observation` projects the angle and
two momentum fields and equates them directly to `Motion.movePlayer cmd`.
`completeMotion_engine_projection` justifies ignoring the Lean function's
animation frame update for this observation; it does not prove the original
animation code.

`motion_establishes_side` derives all sideways-thrust inputs from one initial
relation. In particular, it carries the momentum produced by forward thrust,
the command actually loaded into DH, and the original table invariant through
the previous stores. `MoveMotionInputs` extends the earlier initial relation
with separation of the table pointer, table entries and player pointer from
writes that would otherwise corrupt the subsequent sideways reads. These are
initial data/layout conditions, not assumptions that the desired result holds.

## Original bytes and proof boundary

The certificate binds **213 contiguous bytes / 69 decoded instructions**, from
code-object offset `0x33169` (file offset `0x7517d`) through `0x3323d`, to the
pinned shareware executable with SHA-256:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

Extraction checks all six LE data relocations. Sixty-nine is a sufficient
instruction budget; branches can execute fewer instructions. Relative offset
213 is the sole exit of the combined region.

The proof uses the project's limited x86 semantics: flat total byte memory,
32-bit arithmetic, immutable code and data-object-relative operands. The
executable extraction, relocation checks, original sine-table extraction and
compiled-table comparison are separate tooling checks. DOS loading and
segmentation, memory faults, interrupts, physical timing, and Lean compilation
and runtime are outside the theorem.

The function prologue/epilogue, animation/state-setting call, collision,
friction, position integration, the rest of the tic, and rendering remain
outside this result. This is specifically angle and momentum correspondence
for `P_MovePlayer`'s motion region, not a complete movement-physics proof.

## Validation

```sh
./scripts/verify-original-move-motion
python3 -m unittest discover -s tests -p 'test_original_move_motion.py'
# Optional: requires Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_move_motion.py --cross-check
```

The certificate audits the memory theorem, actual-engine observation theorem
and connecting lemmas. The audit permits only `propext`, `Classical.choice` and
`Quot.sound`; it rejects proof holes and unchecked native checker axioms.

The independent Unicorn run passed **132,352 continuous x86 comparisons**:
all 65,536 turn encodings with varied inputs, all 65,536 forward/side command
pairs while grounded, and 1,280 airborne cases. The harness also varies full
32-bit angles and momenta, signed height extremes, initial registers/flags,
unaligned addresses and two relocation bases. It checks final angle/momenta
against the compiled `Motion.movePlayer`, all eight general registers, ZF/SF/OF,
cached ground, the complete dynamic memory page and exact store order. All
10,240 original sine-table entries match the compiled Lean table.

The six new tests cover byte/relocation corruption, strict axiom auditing,
derivation of the side input relation, the actual engine projection, and
rejection of a relation missing the new preservation obligations. Six existing
joined-region tests and 89 fidelity regressions also pass; the interaction
proof still builds. These finite checks support the implementation and
extraction; the universal claim comes from the Lean theorem.

Only proofs, validation tooling, documentation and a diagnostic probe changed.
No game behavior changed, and no complete gameplay replay was rerun here.

The [animation suffix and walking-state call](PLAYER_ANIMATION_PROOF.md) now
have an original-byte proof, and the [joined player proof](PLAYER_JOINED_PROOF.md)
now derives that entry relation from this motion region. The next boundary is
the function wrapper and its caller's initial-state obligations.
