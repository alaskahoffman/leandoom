import Doom.Random

namespace Doom.Wipe

/-- Original `wipe_initMelt` column delays. Even though melt drawing processes
two-pixel columns, initialization draws from M_Random once per screen pixel
column. These cosmetic draws also affect later status-face choices. -/
def initialDelays (width : Nat) (random : DoomRandom) : Array Int × DoomRandom := Id.run do
  if width == 0 then return (#[], random)
  let (first, next) := random.nextMisc
  let mut rng := next
  let mut y := -(Int.ofNat (first % 16))
  let mut columns := #[y]
  for _ in [1:width] do
    let (value, next) := rng.nextMisc
    rng := next
    y := y + Int.ofNat (value % 3) - 1
    if y > 0 then y := 0
    else if y == -16 then y := -15
    columns := columns.push y
  return (columns, rng)

end Doom.Wipe
