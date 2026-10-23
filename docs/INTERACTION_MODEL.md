# E1M1 interaction model

The live comparison worker now interprets a HITree built from the actual Lean
engine. It uses the unmodified `HITrees.Basic` core from the authors' Lean
development of [HITrees: Higher-Order Interaction Trees](https://arxiv.org/abs/2510.14558),
pinned to commit `3ddf725488a8b2e83af391a1c6ad77796c904865`. The source and
BSD-3-Clause notice are in `vendor/hitrees`; no network fetch is needed to build.

This is the initial engine/model correspondence layer. It is not a proof that
E1M1 matches DOS for every input. The original-binary semantics and subsystem
simulation obligations are still separate work.

## Shared computation

`Doom/Engine.lean` extracts the former live worker's computation into pure
functions. `Context` holds immutable assets and the presentation profile.
`State` includes the entire simulation, fuzz phase, previous indexed frame
(including heap and status widgets), and all three DOS video pages.

`start` loads E1M1 from the supplied WAD lumps and initializes the simulation and
optional DOS heap. `advance` runs the real `Simulation.tickCommand` and
`drawIndexedFrame`. It returns a presentation and the pending state. The
presentation contains the existing pre-render JSON snapshot, exact RGB bytes,
tic number and output-only heap diagnostics. `afterPresent` performs the opening
wipe's state effects after the first frame: RNG consumption, page initialization,
and heap operations. A failure after presenting a frame does not erase that frame.

`LiveRenderProbe.lean` supplies parsed commands, writes frames to its existing
pipe protocol, and handles diagnostic logs. Its `serve` interpreter executes the
tree in `Doom/Interaction.lean`. It contains no duplicate movement or drawing
implementation. The SDL viewer is not migrated to this interaction interface.

## Effects and unbounded iteration

The game uses three requests:

| Request | Meaning |
| --- | --- |
| `input` | Obtain the next `Ticcmd`; every possible response has a continuation. |
| `present frame` | Emit one exact frame and receive an acknowledgement. |
| `again state events` | Internally transfer to the next iteration with the complete state; emit diagnostic heap events to the optional log. |

The result is either `exited tic` or `fault message`. Real engine failures are
explicit returned results, never `unreachable`. Unreachable branches only reject
ill-typed effect responses (a command supplied to a frame acknowledgement, for
example); the interpreters do not take those branches.

HITrees are inductive. A finite term represents the current iteration; the
`again` effect supplies explicit, defunctionalized tail recursion. Its
interpretation re-enters `program`. This is a specialized recursion effect, not
the upstream `RecE` implementation, and it requires no higher-order or concurrency
effects for this sequential engine. There is no global bound on loop iterations.

`Run` gives the operational meaning as a relation over finite observations:
input consumes exactly one command, presentation emits exactly one frame, and
`again` unfolds without consuming a command. Exhausting supplied inputs records
the residual waiting tree, so a finite prefix is not mistaken for game exit.
Inputs remaining after exit or fault are retained explicitly. This supports
arbitrary finite prefixes of ongoing play; we have not yet added an infinite-run
bisimulation theorem or imported the original ITree `eutt` theory. The distinction
between syntax and its interpretation follows the newer paper's approach.

RNG, allocation, rendering history and game time remain deterministic internal
state. Frame events remain observable and ordered. They are not abstracted away
as silent computation.

## Kernel-checked claims

`Doom/Proofs/Interaction.lean` contains:

- `interaction_run_unique`: fixed tree and inputs have at most one completed
  finite-prefix interpretation.
- `interaction_replay_sound`: for every `Engine.State`, `Context`, and finite
  list of `Ticcmd`, the HITree has the recording computed by direct replay through
  `Engine.advance` and `Engine.afterPresent`.
- `interaction_replay_iff`: that recording is exactly the direct replay, with no
  additional alternative results allowed by `Run`.

These quantify over command lists of arbitrary length, not a saved trace or
fixed test bound. They include errors and level exit, and do not assume that
unsupported gameplay paths succeed. They prove equality of the full recording,
including frames, pending input continuation and unconsumed commands. They do
not assert that every possible state is a valid or DOS-corresponding state.

Build with:

```sh
./scripts/lake build Doom.Proofs.Interaction live-render-probe
```

The normal `scripts/test` command also builds the proofs. The theorem about
direct replay is a structural induction over inputs; uniqueness is an induction
over the operational execution derivation. Neither uses `sorry`, a new axiom,
native evaluation, or an assumed DOS step-correspondence theorem.

## Scope still to prove

The formal claim connects two interpretations of the same Lean engine. The
refactor from the old worker is checked by executable regression, not a universal
proof about the old source. The OS pipe handler, parser/serialization, Lean
compiler/runtime, and physical display are outside the theorem. The current
profile is silent, one 320×200 presentation per tic; audio samples, arbitrary
display schedules, menus and intermission are not included. Level reload remains
an explicit DOS-profile error, as before.

The next DOS correspondence layer must define an independently justified
original-machine execution, relate its full state to `Engine.State`, establish
initial correspondence, and prove input/update/presentation steps preserve that
relation. The interaction interface provides a place to compose those proofs;
it does not supply them automatically.

## Refactor validation

The saved 3,426-tic manual exit run remains exact against the original DOS
executable: zero differing pixels, matching declared gameplay fields, and a
byte-identical original state trace. Running the old and new workers on all
3,426 commands in both DOS and Chocolate presentation modes produces identical
JSON/RGB packets and heap diagnostic logs. Ten EOF/invalid-input/partial-output
transport cases also match.

The 98 Lean checks pass. The 494-test Python suite initially caught six duplicated
wipe diagnostic events introduced by the refactor; the other 493 tests passed.
After fixing event-buffer clearing, both heap regression tests pass on rerun,
and the final worker passes both full before/after comparisons and the DOS replay.
The new proofs compile and their axiom audit lists only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

Local evidence, including final executable/source hashes, is preserved in
`artifacts/hitrees-integration/verification.json`. Original game assets and
the local pre-refactor executable are not added to source control.
