import Doom.Weapon
import Doom.Proofs.Firing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.WeaponActions

/-- The two supported windup-to-discharge transitions in the pinned table. -/
def windup : Fire.Gun → Nat | .pistol => 13 | .shotgun => 21
def firing : Fire.Gun → Nat | .pistol => 14 | .shotgun => 22
def duration : Fire.Gun → Int32 | .pistol => 6 | .shotgun => 7
def flashFrame : Fire.Gun → Nat | .pistol => 17 | .shotgun => 30
def flashDuration : Fire.Gun → Int32 | .pistol => 6 | .shotgun => 3
def event (gun : Fire.Gun) (refire : Int32) : Weapon.Event :=
  match gun with | .pistol => .pistol (refire == 0) | .shotgun => .shotgun

def entered (gun : Fire.Gun) (c : Weapon.Context) : Weapon.Context :=
  Weapon.fireAction gun { c with state := { c.state with
    weapon := { c.state.weapon with frame := firing gun, tics := duration gun } } }

/-- Neither supported discharge invokes a recursive continuation. Quantifying
all three callbacks prevents an opaque recursive function supplying the result. -/
theorem terminal_entry (gun : Fire.Gun) (c : Weapon.Context)
    (again : Weapon.Context → Nat → Weapon.Context) (shoot : Weapon.Context → Weapon.Context)
    (check : Weapon.Context → Bool × Weapon.Context) :
    Weapon.enterWith again shoot check c (firing gun) = entered gun c := by
  cases gun <;> simp [Weapon.enterWith, entered, firing, duration, Weapon.fireAction,
    WeaponData.frames, WeaponData.PISTOLFLASH, WeaponData.SGUNFLASH1, Fire.Gun.ammoIndex,
    Fire.discharge, Fire.Gun.pellets]

theorem live_entry (gun : Fire.Gun) (c : Weapon.Context) :
    Weapon.enter c (firing gun) = entered gun c := by
  exact terminal_entry gun c _ _ _

/-- Complete production weapon tick at the discharge boundary. The existing
queue is cleared, a single gun event is produced, and the new flash is ticked
immediately. No assumption about the callback result is an input. -/
theorem live_tick (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = windup gun) (timer : c.state.weapon.tics = 1) :
    Weapon.tick c =
      let fired := entered gun { c with events := #[] }
      { fired with state := Weapon.tickFlash fired.state } := by
  cases gun <;>
    simp [Weapon.tick, frame, timer, windup, WeaponData.frames, Weapon.enter,
      Weapon.enterWith, entered, firing, duration, Weapon.fireAction,
      WeaponData.PISTOLFLASH, WeaponData.SGUNFLASH1, Fire.Gun.ammoIndex, Fire.discharge, Fire.Gun.pellets]

theorem action_ammo (gun : Fire.Gun) (c : Weapon.Context) :
    (Weapon.fireAction gun c).player.ammo[gun.ammoIndex] = c.player.ammo[gun.ammoIndex] - 1 := by
  cases gun <;> simp [Weapon.fireAction, Fire.Gun.ammoIndex, Fire.discharge]

/-- Full-width subtraction, including signed wraparound. -/
theorem action_ammo_bits (gun : Fire.Gun) (c : Weapon.Context) :
    (Weapon.fireAction gun c).player.ammo[gun.ammoIndex].toBitVec =
      c.player.ammo[gun.ammoIndex].toBitVec - 1 := by
  rw [action_ammo]; rfl

theorem action_other_ammo (gun : Fire.Gun) (c : Weapon.Context) (i : Fin 4)
    (other : i ≠ gun.ammoIndex) :
    (Weapon.fireAction gun c).player.ammo[i] = c.player.ammo[i] := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> cases gun <;>
    simp_all [Weapon.fireAction, Fire.Gun.ammoIndex, Fire.discharge]
  all_goals change (c.player.ammo.set! _ _)[3] = c.player.ammo[3]
  all_goals rw [Vector.getElem_set!]; rfl

/-- Observable action outputs after the same-tic flash countdown. -/
theorem tick_outputs (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = windup gun) (timer : c.state.weapon.tics = 1) :
    (Weapon.tick c).events = #[event gun c.state.refire] ∧
    (Weapon.tick c).state.weapon.frame = firing gun ∧
    (Weapon.tick c).state.weapon.tics = duration gun ∧
    (Weapon.tick c).state.flash.frame = flashFrame gun ∧
    (Weapon.tick c).state.flash.tics = flashDuration gun ∧
    (Weapon.tick c).state.extraLight = 1 ∧
    (Weapon.tick c).state.flash.x = c.state.weapon.x ∧
    (Weapon.tick c).state.flash.y = c.state.weapon.y ∧
    (Weapon.tick c).body = (PlayerAnim.enter 155).1 := by
  rw [live_tick gun c frame timer]
  have pistol : (Fire.Gun.pistol == Fire.Gun.shotgun) = false := by decide
  have shotgun : (Fire.Gun.shotgun == Fire.Gun.shotgun) = true := by decide
  cases gun <;> simp [entered, Weapon.fireAction, Weapon.tickFlash, event, firing,
    duration, flashFrame, flashDuration, WeaponData.frames,
    WeaponData.PISTOLFLASH, WeaponData.SGUNFLASH1, pistol, shotgun]

/-- Debit in the actual production tick, not only the isolated action helper. -/
theorem tick_ammo (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = windup gun) (timer : c.state.weapon.tics = 1) :
    (Weapon.tick c).player.ammo[gun.ammoIndex] = c.player.ammo[gun.ammoIndex] - 1 := by
  simp only [live_tick gun c frame timer, entered, action_ammo]

theorem tick_other_ammo (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = windup gun) (timer : c.state.weapon.tics = 1)
    (i : Fin 4) (other : i ≠ gun.ammoIndex) :
    (Weapon.tick c).player.ammo[i] = c.player.ammo[i] := by
  simp only [live_tick gun c frame timer, entered, action_other_ammo gun _ i other]

/-- The earlier discharge arithmetic proof now constrains the real firing tick. -/
theorem tick_spends_one (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = windup gun) (timer : c.state.weapon.tics = 1)
    (loaded : 0 < c.player.ammo[gun.ammoIndex].toInt) :
    (Weapon.tick c).player.ammo[gun.ammoIndex].toInt = c.player.ammo[gun.ammoIndex].toInt - 1 ∧
    0 ≤ (Weapon.tick c).player.ammo[gun.ammoIndex].toInt := by
  rw [tick_ammo gun c frame timer]
  exact discharge_spends_one gun c.player.ammo[gun.ammoIndex] loaded

end Doom.Proofs.WeaponActions
