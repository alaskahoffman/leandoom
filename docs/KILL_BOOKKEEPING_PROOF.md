# Lethal player damage through the weapon CALL

`Doom.Proofs.OriginalKillBookkeeping` extends the continuous lethal floor-damage
proof from corpse setup to the original `P_DropWeapon` call target, `0x2d2c0`.
The theorem starts at any of the three original floor-damage CALL sites. It
preserves the earlier health, armor, damage-count, attacker and corpse-height
results while proving the following additional effects:

- environmental kills increment player zero's kill count exactly when the
  game is not a netgame and the target has `MF_COUNTKILL`;
- the victim's self-frag counter increments, with original 32-bit wraparound;
- the player becomes dead and the body loses `MF_SOLID`;
- the real weapon CALL receives the victim's player pointer in EAX and saves
  return address `0x2a38c` on the byte-addressed stack;
- memory outside the combined write footprint remains unchanged.

All four player slots are covered. The proof executes the original subtraction,
sign extension and signed division by the 280-byte player structure size to
compute the frag index. It does not replace that calculation with an assumed
index. The null source is derived through the earlier damage/kill call chain.

The instruction bound is 158: the previous bound of 131 plus at most 27
bookkeeping/CALL instructions. ESP at the new boundary is the original floor-call
ESP minus 56. This is a bound for one execution of this code path, not a limit
on the values quantified by the theorem.

## Live-engine connection

The existing credit and immediate player-death block in `Death.kill` is now
`Death.bookkeeping`, called directly by the live handler after `Death.corpse`.
The proof compares against this function, including its weapon-lowering event.
The extraction preserves the existing order of credit, self-frag, dead-state,
solidity and event updates. Automap handling remains after the helper.

`live_fields` proves the helper's results for every body/world satisfying the
null-source and player-identity conditions. `live_result` connects those fields
to the decoded original instructions. `joined_execution` composes this with the
previous lethal-damage theorem and transports the initial memory contracts to
the new boundary. It does not assume the desired intermediate results.

The contract requires correct initial field encodings, player identity, ordinary
player metadata, and explicit separation of live fields from stack and other
writes. The additional player-array pointer relation is required for the
original frag-index arithmetic. The full `Simulation.killPlayer` adapter's
construction of these inputs remains a separate obligation.

## Bytes, validation and trust boundary

The manifest `tests/reference/original-kill-bookkeeping.json` adds the original
166-byte region `[0x2a2e6, 0x2a38c)` to the preceding extracted units. The verifier
checks bytes, file locations and relocations against the pinned executable and
generates a kernel-checked certificate using those bytes. The non-null-source
branches are present in the bytes but are outside this theorem's scope.

The small x86 model now decodes immediate byte-register AND and the required
register SUB encoding. Flag information not modeled by existing operations is
still discarded; no proof claims complete processor-state equivalence. Decoder
and execution tests check byte-register masking and preserve unaffected bytes.

```sh
./scripts/verify-original-kill-bookkeeping
# With Unicorn and local JIT access:
python3 scripts/verify_original_kill_bookkeeping.py --cross-check
python3 -m unittest discover -s tests -p test_original_kill_bookkeeping.py -v
```

The universal guarantee comes from the Lean theorem under its premises. Emulator
comparisons are independent supporting evidence: 11,808 original-byte runs,
including 1,468 lethal runs to the actual weapon CALL, compare against compiled
`PlayerDamage.apply`, `Death.corpse` and `Death.bookkeeping`. Checks cover ordered
writes and dynamic memory, both relocated data bases, all four player slots,
netgame branches, signed counter extremes, wrapping object addresses and signed
corpse heights. Rejected and surviving runs retain their earlier boundaries.

The extracted-byte certificate audits 27 declarations and accepts only
`propext`, `Classical.choice` and `Quot.sound`; it contains no `sorry` or native
evaluation axioms. The two bit-mask facts use explicit bit-vector lemmas.
All five new certificate/decoder/execution tests, five preceding kill-entry
tests and eleven live death regressions pass (21 total). New native Lean
fixtures exercise 800 bookkeeping paths, including wrapping stacks; decoder
fixtures exercise every byte value in all eight byte registers. Negative
certificates reject altered instruction bytes, missing contracts, a removed
lethal premise and a changed skill.

## Remaining work

The separate [weapon-lowering action proof](WEAPON_LOWER_PROOF.md) now covers
`A_Lower` for a dead player through its RET to the setter. The
[weapon-drop continuation](WEAPON_DROP_PROOF.md) now composes the enclosing
weapon/setter calls and their returns with this continuous proof.

The theorem stops on entry to `P_DropWeapon`. It proves the call and its
arguments; the linked continuation proves the callee's weapon-state effects. Automap,
death-state selection/actions, timing RNG and the kill/damage returns are next.
The loader/extractor, flat machine model and compiler/runtime boundaries remain
as documented in the earlier proofs. This does not establish whole-tic,
whole-game, or all-input pixel equivalence.
