# Preparation through secret-sector return

`SectorJoined.observation` joins player preparation and the secret-sector caller
into one original-byte execution. It starts at DOS code-object offset `0x333b1`
and returns from the sector handler at `0x333e5`, with an instruction budget of
256. All input contracts describe the initial state; no intermediate memory,
registers, flags, or saved return addresses are supplied at the join.

The observation proves:

- all eleven preparation fields equal `PreparedState.expected`: angle,
  horizontal momenta, animation/state tics, reaction timer, four view fields,
  and cached grounding;
- the sector special and secret counter equal `LevelSpecials.secret 9 z floor n`;
- caller ESP and the EDX player pointer are restored;
- execution reaches the instruction after the original sector CALL.

This covers an initially secret sector, both on and off its floor. The sector
floor is a separate input from the collision-floor value used by preparation.
The existing preparation proof connects its expected fields to live
`Player.prepareTick` under additional scene/actor assumptions. This new theorem
uses that same preparation specification and the live secret helper. The
[runtime extension](PLAYER_SECTOR_RUNTIME_PROOF.md) now connects this result
to the actual preparation/secret phase in `Simulation.interactionTick`, under
explicit scene, actor, and initial sector-lookup premises.

## Joining the machine executions

Preparation previously used PCs relative to `0x30ea0`. The preparation chain
now uses absolute DOS code-object offsets, matching the sector handler. This
changes the words actually pushed by CALL in the formal execution, rather than
changing just a reported PC after execution. For example, movement returns to
`0x333c9`, height returns to `0x333d0`, and the sector handler returns to
`0x333e5`. The nested walking-state call returns to `0x3325e`.

`X86CodeMemory.lift_routine` embeds an existing routine execution into the
interpreter that supports the handler's CS-relative jump table. The embedding
preserves the full state. Its instruction premise excludes `jumpCode`, whose
meaning differs between the interpreters. `preparation_ordinary` proves this
premise for the decoded preparation regions, including every possible byte
offset. The actual jump table is then interpreted with explicit code memory.

`transport` derives the handler's input relation using preparation's memory
frame and restored player/stack registers. `handler_frame` proves the handler
preserves the preparation fields. `execution` composes both machine paths;
`observation` projects the helper results.

## Initial contract

`SectorJoined.Inputs` has four explicit components:

1. `preparation`: the existing preparation entry relation, table contents,
   encoded inputs, and memory-separation conditions.
2. `sector`: initial sector special 9, encoded body Z, sector floor and secret
   count, disjoint secret fields, and handler reads separate from its stack.
3. `sectorReads`: preparation writes cannot corrupt the handler's initial
   pointer chain, body Z, floor, special, or counter.
4. `preparedReads`: handler stack/secret writes cannot corrupt any of the
   eleven preparation fields.

These are sufficient conditions, not a proof that every reachable game state
satisfies them. Word-read protection conservatively covers four bytes at the
special-field address even though the original special read/write is 16-bit.

## Certificate and checks

The certificate binds ten extracted regions (including the switch table) to
DOOM 1.9 shareware executable SHA-256
`b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27`.
It checks both code-object and data-object relocations.

```sh
./scripts/verify-original-sector-joined
python3 -m unittest discover -s tests -p 'test_original_sector_joined.py'
python3 scripts/verify_original_sector_joined.py --cross-check
```

The independent comparison runs original machine bytes continuously in Unicorn
and compares against compiled Lean preparation and secret helpers. The 52,052
cases cover 17,351 on-floor and 34,701 off-floor paths, reaction skips and
movement, nested walking-state calls, two data relocation bases, and all four
byte alignments. Checks include the whole dynamic memory page, preserved
registers, cached grounding, actual return words, and ordered handler writes.
Finite emulator checks validate the harness and semantics independently; they
do not substitute for the universal, conditional Lean theorem.

Validation passed: **16 audited declarations**, using only `propext`,
`Classical.choice`, and `Quot.sound`; **90 focused player/sector regression
tests**, including five new joined-proof tests; and the **52,052 continuous
comparisons** above. The migrated animation and complete movement-function
harnesses also passed **196,608** and **199,168** original-byte comparisons,
respectively. The five new tests check the extracted certificate and strict
axiom audit, mutations in all ten regions, all four required initial contracts,
actual CALL targets/return words, and the interpreter-embedding restriction.

## Remaining work

This closes the preparation-to-secret-handler join. The
[runtime phase connection](PLAYER_SECTOR_RUNTIME_PROOF.md) is also complete
under its stated premises. Other sector types, damage/RNG calls, construction
and preservation of the scene/DOS state relation, reachable-state invariants,
the rest of the player tic, rendering, and whole-game parity remain open. The theorem also relies on the explicitly modeled x86 subset and does
not prove the DOS loader, full EFLAGS, interrupts/timing, or Lean compilation.
