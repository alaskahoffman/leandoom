# Lethal player damage through corpse setup

`Doom.Proofs.OriginalKillEntry.lean` connects the existing damage proof to the
start of `P_KillMobj`. Its continuous execution begins at one of the three
original floor-damage CALL sites and, for an actual lethal `PlayerDamage.apply`
result, reaches `0x2a2e6` after the kill call, its prologue and corpse setup.

This is the first death-handler component. It stops **before** kill-credit and
player-death bookkeeping, weapon lowering, death-state selection, RNG timing,
and the kill/damage returns. It does not complete the lethal branch yet.

## Guarantees at this boundary

Under the initial encoding, metadata and memory-separation premises, the theorem
establishes:

- the kill call receives the original target and the null environmental source;
- the handler saves its five registers on the actual byte-addressed stack;
- the player loses `MF_SHOOTABLE`, `MF_FLOAT`, `MF_SKULLFLY` and `MF_NOGRAVITY`;
- `MF_CORPSE` and `MF_DROPOFF` are set, with other flag bits preserved;
- height is quartered by the original signed arithmetic shift;
- the previously proved armor, player/actor health, damage-count and attacker
  results survive the continuation;
- memory outside the combined stack/gameplay write footprint is preserved.

ESP is now the original floor-call ESP minus 52 bytes. ECX contains the null
source and EBX the target. These are continuation facts, not a claim that the
handler has returned or restored its registers. Player solidity is cleared in
the later player-specific block, outside this theorem.

## Connection to live Lean

The existing initial transformation in `Death.kill` was extracted without a
behavior change into `Death.corpse`. The live handler calls that helper, and
`corpse_fields` relates the original stores to its actual flags/height result.
For example, height `-1` stays `-1`: signed shifting rounds downward rather
than truncating division toward zero.

The main `joined_execution` theorem combines the earlier 108-instruction damage
bound with the three-instruction kill handoff, seven-instruction prologue and
13-instruction corpse block. The resulting 131-instruction bound applies to one
call, not to a bounded playthrough or a finite sample of possible states.

`live_correspondence` packages the final memory projection as the combination of
the actual `PlayerDamage.apply` result and `Death.corpse` result. Lethality is
its only outcome premise; the proof derives that the hit was accepted. The null
source is read from the real damage prologue's saved memory, not supplied as an
assumption about an intermediate register.

The body input is related to the initial machine flags and height. Establishing
that relation for the complete `Simulation.killPlayer` adapter remains separate;
this theorem does not verify all of that wrapper's state construction and scene
effects. Original type zero and Lean kind zero identify the player. The lost
soul's gravity exception is intentionally outside this player theorem.

## Bytes and machine semantics

`tests/reference/original-kill-entry.json` extends the actor-health manifest with
the 11-byte kill handoff and 54-byte corpse/prologue region. The verifier checks
their location, bytes and relocation information against the pinned executable,
along with all preceding damage code.

The flat x86 model gained the two required encodings: byte-memory AND and
register-immediate OR. They retain the distinction between the original byte
store and word stores. The isolated execution theorem models memory in actual
instruction order; separation is introduced only when relating those writes to
independent live fields. Unsupported encodings continue to fail closed.

## Reproduction and evidence

```sh
./scripts/verify-original-kill-entry
# With Unicorn and local JIT access:
python3 scripts/verify_original_kill_entry.py --cross-check
python3 -m unittest discover -s tests -p test_original_kill_entry.py -v
```

The extracted-byte certificate passes a strict audit of 30 declarations, using
only `propext`, `Classical.choice` and `Quot.sound`. The universal result is the
kernel-checked theorem under its premises; the following tests are independent
supporting evidence.

The emulator comparison passes 11,808 damage cases. All 1,468 lethal cases
execute continuously through corpse setup; the other cases stop at their
existing rejection or survival boundary. Expected health/armor results come
from compiled `PlayerDamage.apply`, and flags/height from compiled `Death.corpse`.
Checks include exact ordered writes, dynamic memory, argument registers and
stack movement, all three floor sites, two relocated data bases, four alignments,
wrapping object addresses and ten signed heights including both extremes.

Native fixtures cover 5,760 continuous lethal paths, wrapping stacks and the
excluded lost-soul branch. Decoder/semantics tests cover all 256 byte values,
neighbor-byte preservation, flags and malformed/unsupported encodings.
Negative certificates reject modified calls, flag masks, shifts and stack
instructions, missing contracts, a removed lethal premise and a changed skill.
All five focused tests, ten actor-health/rejected-damage regression tests and
eleven live death tests pass (26 total). The live death probe rebuilds successfully.

## Next composition

The [kill-bookkeeping continuation](KILL_BOOKKEEPING_PROOF.md) now connects
`0x2a2e6` through environmental kill credit, self-frags, solidity and dead state
to the real weapon-lowering CALL. The weapon callee, death-state entry, timing
randomness and the two returns remain open.
The existing flat-machine, external loader/extractor and compiler/runtime trust
boundaries still apply. This is not yet a full player-tic or whole-game proof.
