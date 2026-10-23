# Surviving floor-damage call through the handler return

`Doom.Proofs.OriginalDamageReturn.lean` connects an original ordinary-floor
damage CALL to the instruction immediately after that CALL, for accepted,
nonlethal player damage. This includes the existing guards, armor and health
bookkeeping, disabled-device tactile call, gameplay RNG, pain choice, and
optional pain-state CALL/RET, followed by the remaining null-source bookkeeping
and the damage handler's own RET.

The theorem is conditional on the initial memory relation and on the actual
`PlayerDamage.apply` result being applied and nonlethal. It includes both pain
and no-pain outcomes, zero damage and the signed arithmetic domain of the
preceding proofs. It is not restricted to a recorded input sequence.

## Return-boundary guarantees

For each of the three original floor CALL sites, the continuous run:

- clears the player's reaction timer;
- takes the player/null-source path without retargeting;
- releases the local stack space and restores EBP, EDI and ESI;
- returns through the CALL-written address to `callSite + 5`, with ESP restored;
- preserves the previously established damage, RNG, hit-flag and animation results;
- preserves every memory read outside the accumulated write footprint.

`live_correspondence` reads the health, armor, damage count, attacker, RNG,
hit flags, animation fields and reaction timer from memory **after RET**. These
match the live damage result and animation relation. Scratch EDI is restored by
the epilogue, so the new observation no longer uses it as a remaining-damage
result. EAX, ECX and EBX are not falsely claimed to be callee-saved.

The instruction bound is 166: the previous 152-instruction bound plus at most
14 tail/return instructions. These are bounds for one damage call, not bounds
on gameplay or an exhaustive state search.

## Saved memory across the composition

The previous player-health, actor-health, RNG, pain-handoff and pain-setter
proofs now additionally carry a memory frame relative to the actual prologue's
saved memory. Their original public execution theorems remain available.

This stronger frame distinguishes the initial stack writes from subsequent
writes. It proves that the saved source, registers and return address survive
the intervening calls. `saved_slots` derives their values from the real CALL and
pushes, including unaligned and wrapping stack layouts. No intermediate stack
contents or successful return is assumed.

The additional initial premises specify player type zero, preservation of that
metadata, and byte-level separation of the saved stack and observed fields from
later writes. The source remains the null source established by the original
floor-call relation. The two threshold branches are both covered: a nonzero
threshold exits immediately for a player; a zero threshold reads and rejects
the null source before exiting.

## Live behavior fix

The original clears `reactiontime` on accepted surviving damage even when no
pain state is selected. The live damage wrapper previously omitted this write.
`PlayerDamage.Result.reactionTime` now expresses that rule, and
`Combat.hurtPlayer` uses it for the player's movement reaction timer.

Rejected and lethal damage preserve the incoming timer. The reset is independent
of the pain RNG outcome and applies even to accepted zero damage. This is a
small gameplay correction exposed by extending the proof; a player whose timer
is already zero behaves identically. The formal return theorem relates the
helper to the original store. Verification of the entire `Combat.hurtPlayer`
wrapper, scene synchronization and all other effects remains a separate step.

## Reproduction and evidence

```sh
./scripts/verify-original-damage-return
# With Unicorn and local JIT access:
python3 scripts/verify_original_damage_return.py --cross-check
python3 -m unittest discover -s tests -p test_original_damage_return.py -v
```

The certificate extracts the 111-byte tail region from the pinned executable,
checks its data relocation, and rechecks all earlier code and table bytes. Its
36-declaration audit permits only `propext`, `Classical.choice` and `Quot.sound`.

The independent emulator comparison passes 12,576 cases. Of these, all 968
accepted surviving cases execute the complete handler return, including 964
pain and four no-pain outcomes. Rejected and lethal cases retain their prior
stopping points. Checks cover seven reaction-timer values including signed
extremes, both threshold branches, arbitrary target words, two data bases, four
alignments, wrapping object addresses, exact ordered writes, dynamic memory,
restored registers and return addresses. Reaction expectations come from the
compiled live Lean helper.

Native fixtures cover 9,216 surviving paths over every RNG index, all three
CALL sites, four alignments and positive/zero/negative damage. Negative tests
check instruction mutations, missing contracts, removal of the survival
premises, unsupported retargeting and incorrect return addresses. A separate
runtime fixture calls the real `Simulation.hurtFromFloor` wrapper over every RNG
index and four initial timers, checking both pain outcomes, protected damage and
no-damage tics. The six focused tests and 16 related health/pain/damage regression
tests pass (22 total); the live combat module also rebuilds successfully.

## What remains

This closes the accepted surviving ordinary-floor damage call. The subsequent
[nonlethal return proof](DAMAGE_REJECTED_PROOF.md) adds rejected-path returns and
combines both outcomes. Lethal handling, non-environmental damage, later pain
sound actions, and connecting the initial call contracts to the surrounding
complete player tic remain open. In particular this does not yet prove every `P_DamageMobj`
path, a full player tic, rendering or whole-game equivalence.

The flat x86 model, external extraction/loader and Lean compiler/runtime retain
the existing trust boundary. The legacy `OriginalDiv`/`OriginalRandom` API issue
still prevents claiming a complete repository test-suite pass.
