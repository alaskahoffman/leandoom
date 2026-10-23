import Doom.Weapon
import Doom.Verification.X86Memory
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.WeaponFlash
open Verification X86 X86Memory

def Supported (s : Weapon.State) : Prop :=
  s.flash.frame=0 ∨ s.flash.frame=17 ∨ s.flash.frame=30 ∨ s.flash.frame=31

def pointer (id : Nat) : Word := if id=0 then 0 else BitVec.ofNat 32 (0x15a28+28*id)
def observe (s : Weapon.State) : Word × Word × Word × Word × Word :=
  (pointer s.flash.frame,s.flash.tics.toBitVec,s.extraLight.toBitVec,s.flash.x.raw.toBitVec,s.flash.y.raw.toBitVec)

/-- DOS flash-phase specification: 32-bit countdown, the supported original
successors/light actions, then unconditional weapon-coordinate synchronization. -/
def expected (s : Weapon.State) : Word × Word × Word × Word × Word :=
  let id := s.flash.frame
  let timer := s.flash.tics.toBitVec
  let body :=
    if id=0 ∨ timer=0xffffffff then (pointer id,timer,s.extraLight.toBitVec)
    else if timer-1=0 then
      if id=30 then (pointer 31,3,2) else (0,0,0)
    else (pointer id,timer-1,s.extraLight.toBitVec)
  (body.1,body.2.1,body.2.2,s.weapon.x.raw.toBitVec,s.weapon.y.raw.toBitVec)

theorem decrement (v : Int32) : (v-1).toBitVec=v.toBitVec-1 := rfl

theorem live_expected (s : Weapon.State) (supported : Supported s) :
    observe (Weapon.tickFlash s)=expected s := by
  have minus : s.flash.tics=(-1 : Int32) ↔ s.flash.tics.toBitVec=(0xffffffff#32) := by
    constructor
    · intro h; rw [h]; decide
    · intro h; exact Int32.toBitVec_inj.mp h
  have zero : s.flash.tics-1=(0 : Int32) ↔ s.flash.tics.toBitVec-(1#32)=(0#32) := by
    constructor
    · intro h; have hh := congrArg Int32.toBitVec h; exact hh
    · intro h; exact Int32.toBitVec_inj.mp h
  rcases supported with frame|frame|frame|frame <;>
    by_cases forever : s.flash.tics=(-1 : Int32) <;>
    by_cases expires : s.flash.tics-1=(0 : Int32) <;>
    simp [observe,expected,pointer,Weapon.tickFlash,frame,forever,expires,←minus,←zero,
      WeaponData.frames,WeaponData.LIGHTDONE,BitVec.ofNat_eq_ofNat]

end Doom.Proofs.WeaponFlash
