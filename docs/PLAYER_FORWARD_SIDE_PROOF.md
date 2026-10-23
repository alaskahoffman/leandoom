# Forward thrust through the sideways guard

The actual inlined forward-thrust instructions now execute continuously into
the sideways guard in a Lean proof. The guard receives the full machine state
produced by thrust. The proof establishes that the cached `onground` word and
sideways command survive the scratch/momentum writes under explicit byte-range
separation assumptions, and that the guard makes the engine's side-movement
decision. A second theorem covers entry directly at the side guard when forward
thrust was skipped.

This region is now incorporated in the [joined movement proof](PLAYER_MOVE_JOIN_PROOF.md)
under one initial state relation. Both results stop before sideways thrust and
do not establish a complete player tic.

## Original bytes and entry points

The checked slice contains 88 contiguous bytes at code-object offset `0x33199`,
EXE file offset `0x751ad`, in original shareware DOOM 1.9:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

The extractor verifies the bytes and all three LE data-operand relocations:
the cosine pointer, sine table base, and cached-ground address.

| Path | Entry offset | Maximum instructions | Result exits |
| --- | --- | --- | --- |
| Execute forward thrust, then side guard | 0 | 28 | 88 or 165 |
| Skip forward thrust; enter side guard | 72 | 5 | 88 or 165 |

Exit 88 is original address `0x331f1`, the start of sideways thrust. Exit 165 is
`0x3323e`, the animation-selection code after sideways thrust. The latter lies
outside this slice; execution stops there without asserting anything about the
subsequent code.

`original_forward_side` proves the ordered raw memory and branch effects with
no separation premises. `forward_side_matches_engine` strengthens that to the
engine's forward momentum calculation and side-guard condition for every
related entry state. Its memory result includes the scratch word and both
momentum writes, not just two projected numeric results.

`ForwardSideInputs` includes the existing inlined-thrust input relation plus
the cached ground and side-command values. Six separation conditions establish
that neither is overwritten by the scratch, momx, or momy store. The proof
`forward_establishes_side_inputs` derives the guard's inputs after execution;
it does not re-assume their values at the seam. ECX and ESI preservation is
proved from the actual decoded thrust instructions.

The forward-body theorem describes what happens when that entry is used. The
preceding guard decides whether execution should enter there; the joined proof
now derives these premises from the original entry state. The body's angle is the angle at this entry, after
turning in the intended caller.

## Reusable straight-line/control-flow bridge

`Doom/Verification/X86Linear.lean` supplies a generic bridge:

- `decodePackets` records each decoded instruction together with its actual
  byte length, rejecting incomplete or unsupported input.
- `LinearFits` checks the enclosing program's instruction at each PC and ensures
  the proposed linear path does not pass through a declared exit.
- `linear_prefix` constructs an exact execution prefix from those static checks.
- `linear_state` connects its resulting core to the existing `X86Block.eval`
  semantics while retaining the PC and flag projection.

This allows reuse of the existing multiplication/thrust proofs inside a
continuous control-flow proof. Flags invalidated by arithmetic remain unknown;
the side guard's TEST/CMP establishes the flags used by its branches.
The proposed instruction lengths and operations are checked against the
original byte decoder, not trusted as annotations.

## Validation

```sh
./scripts/verify-original-forward-side
python3 -m unittest discover -s tests -p 'test_original_forward_side.py'
```

Optional independent Capstone/Unicorn validation:

```sh
python3 scripts/verify_original_forward_side.py --cross-check
```

The initial independent run passed **73,984 cases**:

- 65,280 nonzero forward-command / side-command pairs;
- 8,192 additional cases covering every fine-angle bin;
- 512 skipped-forward cases covering both ground states and every side command.

The test varies momenta, unused registers, initial flags, unaligned player,
object and scratch addresses, and two relocation bases. It checks continuous
branch exits, compiled-engine momentum, all general registers, ZF/SF/OF, the
dynamic memory page, cached ground and write order. All 10,240 original sine
table entries are also compared with the compiled Lean table. These checks
validate the model independently; they are not the universal proof.

Five new regression tests cover the generated certificate, strict axiom audit,
byte mutations, decoding and linear-path rejection, a false memory-preservation
claim, and extraction/relocations. Existing inlined-thrust and composed-entry
tests also pass. The interaction proof still builds.

The kernel audit permits only `propext`, `Classical.choice` and `Quot.sound`.
Missing audits, native-checker axioms and `sorryAx` are rejected.

## Remaining work

The joined proof now connects the preceding entry region to these premises.
Next connect the side-thrust body and its skipped path. Animation/state calls,
prologue/epilogue, collision and the rest of the tic remain outside this result.

The model still assumes total flat memory and data-object-relative addresses.
DOS loading, segmentation, access faults, physical instruction fetch, interrupts,
timing, and the Lean compiler/runtime are outside these proofs. There was no
engine behavior change or complete gameplay replay in this milestone.
