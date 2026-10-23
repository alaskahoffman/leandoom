# Original reaction-time decision and both movement branches

`PlayerReactionProof.observation` proves the original `P_PlayerThink` reaction
branch and its continuation, under an explicit initial data/layout relation.
It starts at the load of the player's object pointer and ends just before
`P_CalcHeight`, including the complete movement function and its walking-state
call when selected.

The observed angle, both momenta, animation state/timer and reaction timer match
`PlayerReaction.move`, `animate` and `remaining`, which are used by live player
preparation. The final stack pointer is unchanged and EAX again holds the
player pointer, ready for height calculation.

The branch is based on the timer at the beginning of the tic:

- Zero: execute the already-proved movement/animation call sequence. The
  reaction word stays zero.
- Nonzero: decrement the 32-bit timer and skip movement and walking-state entry.
  Angle, momenta and animation fields are preserved. A timer of one becomes
  zero but still skips movement this tic; movement can resume the next tic.

The original TEST checks nonzero, not positive. The theorem includes negative
and extreme signed encodings and the wrapping decrement of `INT32_MIN` to
`INT32_MAX`. These are statements about the pinned machine instructions.

This is not a whole `P_PlayerThink`, height-calculation or whole-tic theorem.
Earlier death/command handling, reachable-state invariants, later rendering,
and timer producers such as teleportation remain separate obligations.

## Proof composition

The 17-byte prefix loads the player object into EAX and reactiontime into ESI,
then tests ESI. These reads leave memory, EDX's player pointer and ESP unchanged.
`establishes_caller` derives the existing call-site relation; it does not assume
another relation about an intermediate machine state.

On the zero path, the proof reuses the full caller/function/return result. A
new `caller_load` frame rule proves that words separated from the caller,
prologue, motion and animation writes survive the entire sequence. It is used
to preserve the reaction word and can be reused for other untouched fields.

On the nonzero path, the original LEA computes ESI minus one, the MOV stores
it into the object, and the short JMP bypasses the movement call. LEA and MOV
preserve the TEST flags; the proof executes the real jump and final argument
reload. It identifies the full modeled output state, including temporary
ESI/EDI changes and the single memory store.

A 124-instruction bound covers the longest composed path. The skipped path
executes eight instructions total. The entry contract includes the prior
caller's data/layout relation, the initial timer encoding and separation of
the timer word from the zero branch's stores.

## Runtime connection

The live path previously had no player reaction timer and always applied
command movement. `Player.reactionTime`, initialized to zero, now flows through
`Player.prepareTick` into `Scene.preparePlayerPhysics`. The latter invokes
`PlayerReaction.move`; the former uses `animate` and `remaining` with the same
**old** timer. The normal zero-timer path keeps its previous behavior.

`Player.cachedOnGround` also preserves the original cached ground flag when
movement is skipped. The physics preparation result updates it only when the
movement branch runs, and passes the retained flag to height calculation.
The independent x86 checks verify the original skipped path leaves the cached
word untouched; the live integration test checks both retained-false and
retained-true cases. The formal observation in this milestone covers the
movement/animation/timer fields, not the subsequent height calculation.

This gates command turning/thrust and walking-state entry. It does not freeze
later momentum integration, actor animation ticking, weapons or the entire tic.
It also does not implement every gameplay action that may set a reaction timer.

## Binding to original bytes

The certificate checks the 26-byte, 10-instruction caller region at original
code offset `0x333b1`, file offset `0x753c5`, the 264-byte movement function and
the 91-byte state setter. All eight data relocations are validated. The pinned
shareware DOOM 1.9 executable SHA-256 remains:

`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`

Using absolute DOS code-object offsets, entry PC is `0x333b1`, and exit PC is `0x333cb`. The
machine decoder adds signed-byte unconditional JMP, with checked relative
PC bounds. No unsupported instruction is treated as a no-op.

The existing modeling limits still apply: flat total memory, immutable code,
partial flags and explicit address conventions. DOS loading, segmentation,
faults, interrupts, physical timing and Lean compilation/runtime are outside
the theorem. The state setter is covered for the selected walking-entry path.

## Validation

```sh
./scripts/verify-original-player-reaction
python3 -m unittest discover -s tests -p 'test_original_player_reaction.py'
# Requires Capstone and Unicorn, including permission for its JIT.
python3 scripts/verify_original_player_reaction.py --cross-check
```

The certificate audits the original bytes, full execution, runtime observation,
caller-relation derivation, nonzero path, timer preservation and reusable frame
rule. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. No proof
holes or unchecked native checker axioms are accepted.

**264,704 independent continuous x86 comparisons passed:** 199,168 zero-timer
cases covering all turn encodings, all forward/side pairs from standing and
running, and airborne cases; plus 65,536 nonzero-timer cases covering every
forward/side pair with varied signed timers, including one, negative values
and both signed extrema. This is independent validation, not an exhaustive
32-bit-timer proof; the Lean theorem supplies the universal conditional claim.

The harness checks the full dynamic memory page, all registers, flags, cached
ground, ordered writes and call/return paths. Nonzero cases must execute no
movement or animation CALL, write only the timer word, and preserve cached
ground. The zero cases preserve the timer and execute the selected nested calls.
Both use varied angles/momenta/heights/animations, unaligned player/object/stack
addresses, and two data relocation bases.

Eight new tests cover certificate/axiom auditing, corrupted branch/decrement/
store/jump bytes, derived inputs and timer observations, missing preservation
premises, all signed-byte JMP encodings and boundary handling, compiled helper
edge cases, actual `Player.prepareTick` behavior across multiple tics, and exact
extraction/relocations. All 104 Python tests passed (8 reaction, 7 caller and 89
fidelity), as did 98 built-in engine checks. The engine, live-render and fidelity
probes, and interaction proof built successfully together (200 build jobs).

The live comparison services were not restarted and no complete gameplay replay
was rerun for this milestone.

## Next boundary

The following `P_CalcHeight` routine and its original CALL/RET are now proved;
see [the height proof](PLAYER_HEIGHT_PROOF.md). `PlayerGround.reaction_ground`
proves that this region refreshes grounding only for a zero reaction timer.
`PlayerHeightJoin.establishes_height` derives the complete height-call input
contract from initial-state premises, including updated momenta and preserved
view fields/tables. `PlayerPreparation.observation` now executes this region and
the height CALL/RET continuously under the same code origin. `PreparedState`
now carries all eleven preparation fields through that call, and
`PreparedRuntime.correspondence` relates them directly to `Player.prepareTick`
under explicit scene and entry premises. The complete player/world-state
relation, later player actions and mobj integration remain to be connected.
