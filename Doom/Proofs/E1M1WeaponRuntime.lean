import Doom.Proofs.E1M1WeaponFlash
import Doom.Combat
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace Doom.Proofs.E1M1WeaponRuntime
open Verification X86 X86Memory X86Control BlockSummary

/-- A property of the production updater, before its event interpreter runs.
Flash expiration is allowed: it changes light/state but emits no weapon event. -/
theorem no_events (s : Simulation) (keys : UInt32)
    (quiet : E1M1WeaponFlash.Quiet s.weapon) :
    (Weapon.tick (s.weaponContext keys)).events = #[] := by
  rw [E1M1WeaponFlash.live_tick _ quiet]

/-- The live Simulation adapter installs exactly the proved Weapon.tick result. -/
theorem installed (s : Simulation) (keys : UInt32)
    (quiet : E1M1WeaponFlash.Quiet s.weapon) :
    (s.weaponTick keys).weapon = (Weapon.tick (s.weaponContext keys)).state := by
  have events := no_events s keys quiet
  simp [Simulation.weaponTick, events]
  all_goals repeat' first | rfl | split

/-- Description of the event-free adapter apart from its diagnostic attack-age
counter, which is deliberately not claimed to correspond to DOS here. -/
def install (s : Simulation) (c : Weapon.Context) (age : Nat) : Simulation :=
  { s with
    weapon := c.state, player := { s.player with animation := c.body },
    inventory := Inventory.fromPickup c.player, weaponAge := age,
    attackDown := c.state.attackDown, refire := c.state.refire != 0 }

/-- Reusable for any event-free weapon update, not just countdowns. It constrains
all Simulation fields except the diagnostic attack-age field. -/
theorem no_events_install (s : Simulation) (keys : UInt32)
    (events : (Weapon.tick (s.weaponContext keys)).events = #[]) :
    ∃ age, s.weaponTick keys = install s (Weapon.tick (s.weaponContext keys)) age := by
  simp [Simulation.weaponTick, events, install]
  all_goals repeat' first | exact ⟨_,rfl⟩ | rfl | split

theorem flash_latches (v : Weapon.State) :
    (Weapon.tickFlash v).refire = v.refire ∧
    (Weapon.tickFlash v).attackDown = v.attackDown := by
  simp [Weapon.tickFlash]
  all_goals repeat' first | exact ⟨rfl,rfl⟩ | rfl | split

theorem countdown_latches (v : Weapon.State) :
    (E1M1WeaponFlash.countdown v).refire = v.refire ∧
    (E1M1WeaponFlash.countdown v).attackDown = v.attackDown := by
  unfold E1M1WeaponFlash.countdown
  split <;> exact ⟨rfl,rfl⟩

/-- The countdown path uses the original inventory adapter and cannot generate
shots, noise alerts, damage, or new audio events. The inventory round-trip is
kept explicit, rather than claiming equality for arbitrary malformed inventories. -/
theorem quiet_install (s : Simulation) (keys : UInt32)
    (quiet : E1M1WeaponFlash.Quiet s.weapon) :
    ∃ age, s.weaponTick keys =
      { s with
        weapon := Weapon.tickFlash (E1M1WeaponFlash.countdown s.weapon),
        inventory := Inventory.fromPickup s.inventory.toPickup,
        weaponAge := age, attackDown := s.weapon.attackDown, refire := s.weapon.refire != 0 } := by
  obtain ⟨age,eq⟩ := no_events_install s keys (no_events s keys quiet)
  refine ⟨age,?_⟩
  rw [eq,E1M1WeaponFlash.live_tick _ quiet]
  simp [install,Simulation.weaponContext, (flash_latches _).1, (flash_latches _).2,
    (countdown_latches _).1, (countdown_latches _).2]

/-- Future-relevant state and logical audio outputs are preserved on this
branch. This is not an audio-sample equivalence theorem. -/
theorem quiet_effects (s : Simulation) (keys : UInt32)
    (quiet : E1M1WeaponFlash.Quiet s.weapon) :
    (s.weaponTick keys).rng = s.rng ∧
    (s.weaponTick keys).audio = s.audio ∧
    (s.weaponTick keys).audioEvents = s.audioEvents ∧
    (s.weaponTick keys).soundTargets = s.soundTargets ∧
    (s.weaponTick keys).shots = s.shots ∧
    (s.weaponTick keys).physicsError = s.physicsError := by
  obtain ⟨age,eq⟩ := quiet_install s keys quiet
  rw [eq]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Close the supported-flash invariant at the runtime boundary. Weapon-state
expiration still needs a separate action proof on the following tic. -/
theorem supported_after (s : Simulation) (keys : UInt32)
    (quiet : E1M1WeaponFlash.Quiet s.weapon)
    (supported : WeaponFlash.Supported s.weapon) :
    WeaponFlash.Supported (s.weaponTick keys).weapon := by
  rw [installed s keys quiet, E1M1WeaponFlash.live_tick _ quiet]
  apply E1M1FlashExpiry.supported_after
  simpa [WeaponFlash.Supported, Simulation.weaponContext] using supported

/-- Binary-to-runtime bridge. The five observed words are the muzzle-flash
state, timer, extra light and coordinates installed in the real Simulation.
Initial representation, quiet-weapon and memory contracts remain explicit. -/
theorem live_correspondence (machine : X86Memory.State) (flags : Option Flags)
    (p : Word) (s : Simulation) (keys : UInt32)
    (h : E1M1WeaponFlash.Inputs machine p s.weapon)
    (quiet : E1M1WeaponFlash.Quiet s.weapon)
    (supported : WeaponFlash.Supported s.weapon)
    (safe : E1M1WeaponFlash.Safe p (machine.regs 4))
    (expiry : ¬ E1M1FlashUpdate.NoTransition s.weapon →
      E1M1FlashExpiry.Tables machine.memory ∧ E1M1FlashExpiry.Separated p (machine.regs 4)) :
    ∃ n t, n ≤ 125 ∧
      X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
        ⟨machine,flags,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p = WeaponFlash.observe (s.weaponTick keys).weapon := by
  rw [installed s keys quiet]
  exact E1M1WeaponFlash.live_correspondence machine flags p (s.weaponContext keys)
    h quiet supported safe expiry

end Doom.Proofs.E1M1WeaponRuntime
