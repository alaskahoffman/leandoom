import Doom.Proofs.E1M1BulletAim
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open OriginalBulletSlope
namespace BulletSlopeFixture
-- Post-query states with unaligned saved frames and arbitrary signed slopes.
def response (present slope angle : Word) : X86Memory.State :=
  {regs := fun r => if r=0 then slope else if r=1 then angle else if r=4 then 1 else if r=6 then 0x600043 else 0,
   memory := store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
     1 11) 5 22) 9 33) 13 44) 17 0x2d966) 0x2b9f8 present}
example : (decision false (response 0x80000000 0 0)).pc=0x2d81e := by decide
example : (decision false (response 0 0x80000000 0)).pc=0x2d7e4 := by decide
example : load32 (E1M1BulletAim.accepted false (response 1 0x80000000 0)).core.memory 0x2c0c0=0x80000000 := by decide
example : (E1M1BulletAim.accepted false (response 1 0 0)).pc=0x2d966 := by decide
example : (E1M1BulletAim.accepted false (response 1 0 0)).core.regs 4=21 := by decide
example : (E1M1BulletAim.nextQuery false (response 0 0 0xffffffff)).core.regs 2=0x03ffffff := by decide
example : (E1M1BulletAim.nextQuery true (response 0 0 0x04000000)).core.regs 2=0xfc000000 := by decide
-- The last miss is not forcibly reset by P_BulletSlope: P_AimLineAttack must return zero.
example : load32 (E1M1BulletAim.lastReturn (response 0 123 0) none).core.memory 0x2c0c0=123 := by decide
example : X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] 9
    ⟨response 1 0 0,none,0x2d7d5⟩ (E1M1BulletAim.accepted false (response 1 0 0)) :=
  E1M1BulletAim.accepted_execution false _ _ (by decide)
example : X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] 8
    ⟨response 0 123 0x04000000,none,0x2d7f8⟩ (E1M1BulletAim.nextQuery true (response 0 123 0x04000000)) :=
  E1M1BulletAim.next_query_execution true _ _ (by decide)
end BulletSlopeFixture
