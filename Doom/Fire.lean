/- Shared discharge accounting for the original pistol and shotgun actions.
No geometry or RNG is moved here: each pellet is still traced and damages its
victim before the next pellet's random draws. -/
import Doom.WeaponData
import Doom.AutoAim
namespace Doom.Fire
inductive Gun where
  | pistol | shotgun
  deriving BEq, Repr, Inhabited

def Gun.pellets : Gun → Nat
  | .pistol => 1
  | .shotgun => 7

def Gun.ammoIndex : Gun → Fin 4
  | .pistol => 0
  | .shotgun => 1

structure Discharge where
  ammoAfter : Int32
  pellets : Nat
  deriving Inhabited

/-- Called by the actual weapon action, using signed wrapping engine arithmetic. -/
def discharge (gun : Gun) (ammoBefore : Int32) : Discharge :=
  ⟨ammoBefore - 1, gun.pellets⟩

/-- Original firing-to-refire-to-firing path, before branching for release,
weapon change, death or ammo exhaustion. Includes next attack's windup. -/
def Gun.cycleFrames : Gun → List Nat
  | .pistol => [WeaponData.PISTOL2, WeaponData.PISTOL3, WeaponData.PISTOL1]
  | .shotgun => [WeaponData.SGUN2, WeaponData.SGUN3, WeaponData.SGUN4,
      WeaponData.SGUN5, WeaponData.SGUN6, WeaponData.SGUN7, WeaponData.SGUN8, WeaponData.SGUN1]

def Gun.cycleTics (gun : Gun) : Nat :=
  (gun.cycleFrames.map fun frame => WeaponData.frames[frame]!.tics.toInt.toNat).sum

structure Sample where
  gun : Gun
  tic : Nat
  ammoBefore : Int32
  ammoAfter : Int32
  pelletsExpected : Nat
  pelletsTraced : Nat := 0
  aim : Option AutoAim.Selection := none
  pelletAngles : Array UInt32 := #[]
  deriving Inhabited
end Doom.Fire
