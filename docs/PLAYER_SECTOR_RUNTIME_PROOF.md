# Original bytes to the live preparation/secret phase

`SectorRuntime.correspondence` connects the joined DOS execution to
`Simulation.prepareSectorTick`, the phase now called by the live
`Simulation.interactionTick`. The result is read from the returned `Player`,
secret count, and updated map sector. It covers eleven preparation fields plus
the sector special and secret counter, for an initially secret sector on or
off its floor.

This strengthens the [joined helper correspondence](PLAYER_SECTOR_JOINED_PROOF.md):
the right-hand side is an actual simulation operation, not a separate composition
of helper calculations. Both sides preserve failure explicitly (`none` for a
failed observation), and the stated entry premises establish successful execution.

## Runtime boundary and implementation

The existing inline sequence was factored into `Simulation.prepareSectorTick`:

1. Copy simulation inventory into the incoming player.
2. Call `Player.prepareTick` with the supplied command.
3. Look up the sector at the prepared player's position.
4. Run secret discovery and store the returned count and sector special.

`interactionTick` calls this phase after its clock/event/button prelude and
before the `sectorEffects` callback, use/weapon actions, counters, and mobj
movement. `Simulation.tick` supplies the walking/live-player gate around the
interaction branch. The new theorem starts at this phase boundary; it does not
prove that gate, prelude, or the remainder of the full tick.

`SectorRuntime.phase_continuation` proves that invoking the factored phase with
any continuation equals the former inline preparation/discovery control flow.
In particular, preparation errors retain the incoming player, while sector
lookup errors retain the already-prepared player. The refactor adds no new
error checks or changes to gameplay calculations.

## What the proof derives

- `position`: reaction delay, turning, thrust and animation preparation leave
  X/Y/Z unchanged for every body, timer and command.
- `prepare`: the actual preparation succeeds, preserves the explicit command,
  produces the established eleven fields, and uses the synchronized collision
  actor's position. The initial `Player.body` may contain different coordinates.
- `phase_execution`: the unchanged actor position supplies the actual sector
  lookup. The exact returned simulation changes only the prepared player,
  secret counter, and selected map sector record.
- `phase_frame`: the returned command, RNG, simulation inventory, tick count,
  error field, sector-array size, and all other sector records are preserved.
- `runtime_observation`: read the eleven fields and two secret fields from that
  actual returned state.
- `correspondence`: combine this with `SectorJoined.execution`, without adding
  assumed post-preparation state or intermediate memory relations.

The secret floor is taken from the selected **map sector**, not the collision
actor's `floorz`. Body Z is also distinct from the calculated eye/view Z.
These distinctions matter when standing above a lower neighboring floor.

## Initial assumptions and remaining work

The theorem takes explicit `Ticcmd` input and assumes:

- inventory-synchronized `Player.syncScene` succeeds;
- the synchronized scene contains a player actor at index zero;
- that actor is not floating;
- the initial map BSP lookup at the actor's X/Y succeeds;
- the returned sector index is in bounds and its special is 9;
- the joined DOS memory/register relation encodes this actor's motion, the
  player's animation/reaction/view state, the selected sector floor, and the
  simulation secret counter, with the existing tables and separation premises.

It does not prove scene synchronization or BSP correspondence with DOS,
construction of the initial DOS state relation, or preservation of these
premises by every reachable game state. Keyboard translation, other sector
effects, full-state/whole-tic equivalence, rendering, and compilation remain
separate obligations. The next extensions can address other sector paths and
the invariants needed to reuse these phase results over successive tics.

## Validation

```sh
./scripts/verify-original-sector-joined
python3 -m unittest discover -s tests -p 'test_original_sector_*.py'
python3 -m unittest discover -s tests -p 'test_level_specials.py'
python3 -m unittest discover -s tests -p 'test_simulation.py'
```

The existing ten-region DOOM 1.9 certificate now additionally binds the live
runtime theorem to the extracted bytes. Its **24 audited declarations** use
only `propext`, `Classical.choice`, and `Quot.sound`, with no proof holes or
unchecked native axioms.

The new runtime tests reject omitted scene/actor/sector premises, incorrect
actor or floor relations, a different output sector, and substituting keyboard
input for the explicit command. An executable Lean fixture exercises actor
versus stale player coordinates, distinct sector/collision floors, nonzero
sector indices, counter wraparound, reaction delay/negative timers, repeat
visits, and both failure stages. Existing secret, simulation and floor-damage
runtime regressions and the native Lean test suite cover the refactor.

All **78 focused Python tests** passed (35 sector-proof, 9 level-special,
30 simulation, and 4 floor-damage runtime tests), along with **98 native Lean
checks**. The proof target, game executable, and test executable built successfully.

The earlier 52,052 independent x86/compiled-Lean comparisons remain validation
of the joined helper composition. They are not newly claimed as direct tests
of the complete simulation wrapper; its connection is the kernel-checked
runtime theorem and the runtime regressions described here.
