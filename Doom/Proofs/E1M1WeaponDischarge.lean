import Doom.Proofs.E1M1WeaponRuntime
import Doom.Proofs.WeaponActions
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1WeaponDischarge

/-- A single emitted event is executed once, even if the result is an error.
The diagnostic age is left existential as in the event-free adapter theorem. -/
theorem single_event (s : Simulation) (keys : UInt32) (event : Weapon.Event)
    (events : (Weapon.tick (s.weaponContext keys)).events = #[event]) :
    ∃ age, s.weaponTick keys =
      (E1M1WeaponRuntime.install s (Weapon.tick (s.weaponContext keys)) age).weaponEvent
        (s.weaponContext keys).player.ammo (Weapon.tick (s.weaponContext keys)).player event := by
  let c := Weapon.tick (s.weaponContext keys)
  let first := Weapon.attackState c.player.readyWeapon.val
  let age := if c.state.weapon.frame ≥ first && c.state.weapon.frame <
      (if c.player.readyWeapon == 0 then 10 else if c.player.readyWeapon == 1 then 17 else 30) then
    (List.range' first (c.state.weapon.frame-first)).foldl
      (fun n f => n + WeaponData.frames[f]!.tics.toInt.toNat) 0 +
      (WeaponData.frames[c.state.weapon.frame]!.tics-c.state.weapon.tics).toInt.toNat
    else 100
  refine ⟨age,?_⟩
  simp [Simulation.weaponTick, events, E1M1WeaponRuntime.install, age, first, c]
  all_goals repeat' first | rfl | split

/-- The actual discharge tic reaches the actual hitscan/sound handler, without
an assumed callback result. All geometry/RNG/damage behavior inside that handler
still needs its own DOS correspondence theorem. -/
theorem firing_dispatch (gun : Fire.Gun) (s : Simulation) (keys : UInt32)
    (frame : s.weapon.weapon.frame = WeaponActions.windup gun)
    (timer : s.weapon.weapon.tics = 1) :
    ∃ age, s.weaponTick keys =
      (E1M1WeaponRuntime.install s (Weapon.tick (s.weaponContext keys)) age).weaponEvent
        (s.weaponContext keys).player.ammo (Weapon.tick (s.weaponContext keys)).player
        (WeaponActions.event gun s.weapon.refire) := by
  apply single_event
  exact (WeaponActions.tick_outputs gun (s.weaponContext keys) frame timer).1

/-- The pistol uses its refire flag; shotgun pellets always use spread. The fire
sample is installed before entering the live handler. This stops at the handler,
not at an assumed successful hit or sound-device output. -/
theorem pistol_event (s : Simulation) (before : Vector Int32 4) (after : Pickup.State)
    (accurate : Bool) :
    s.weaponEvent before after (.pistol accurate) =
      ({s with lastFire := some {
        gun := .pistol, tic := s.ticks, ammoBefore := before[0], ammoAfter := after.ammo[0], pelletsExpected := 1}} : Simulation).fireGun false accurate := by
  rfl

theorem shotgun_event (s : Simulation) (before : Vector Int32 4) (after : Pickup.State) :
    s.weaponEvent before after .shotgun =
      ({s with lastFire := some {
        gun := .shotgun, tic := s.ticks, ammoBefore := before[1], ammoAfter := after.ammo[1], pelletsExpected := 7}} : Simulation).fireGun true false := by
  rfl

/-- Joined production boundary: the ammo value recorded for the shot is the
proved debit, and the real firing handler receives the original accuracy mode.
No result of hitscan, damage or sound synthesis is assumed or proved here. -/
theorem firing_handler (gun : Fire.Gun) (s : Simulation) (keys : UInt32)
    (frame : s.weapon.weapon.frame = WeaponActions.windup gun)
    (timer : s.weapon.weapon.tics = 1) :
    ∃ age, s.weaponTick keys =
      let before := (s.weaponContext keys).player.ammo[gun.ammoIndex]
      let base := E1M1WeaponRuntime.install s (Weapon.tick (s.weaponContext keys)) age
      ({base with lastFire := some {
        gun, tic := s.ticks, ammoBefore := before, ammoAfter := before-1,
        pelletsExpected := gun.pellets}} : Simulation).fireGun
          (gun == .shotgun) (if gun == .pistol then s.weapon.refire == 0 else false) := by
  obtain ⟨age,eq⟩ := firing_dispatch gun s keys frame timer
  refine ⟨age,?_⟩
  rw [eq]
  have ammo := WeaponActions.tick_ammo gun (s.weaponContext keys) frame timer
  cases gun with
  | pistol =>
    simp only [WeaponActions.event, pistol_event]
    change (Weapon.tick (s.weaponContext keys)).player.ammo[0] =
      (s.weaponContext keys).player.ammo[0] - 1 at ammo
    rw [ammo]
    rfl
  | shotgun =>
    simp only [WeaponActions.event, shotgun_event]
    change (Weapon.tick (s.weaponContext keys)).player.ammo[1] =
      (s.weaponContext keys).player.ammo[1] - 1 at ammo
    rw [ammo]
    rfl

end Doom.Proofs.E1M1WeaponDischarge
