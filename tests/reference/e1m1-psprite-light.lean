import Doom.Proofs.E1M1PspriteLight
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
namespace PspriteLightChecks

def record (m : Memory) (id timer next action : Word) : Memory :=
  let a := 0x15a28+28*id
  store32 (store32 (store32 m (a+8) timer) (a+16) next) (a+12) action
def tables := record (record (record (record (fun _ => 0)
  1 0 0 0x2db40) 17 7 1 0x2db50) 30 4 31 0x2db50) 31 3 1 0x2db60

def player (id : Word) : X86Memory.State :=
  ⟨write (write (write (write (fun _ => 0) 0 0x600000) 2 1) 3 id) 4 0x603000,
    store32 tables 0x603000 0x12345678⟩
def observation (t : X86Control.State) :=
  (t.pc,t.core.regs 4,load32 t.core.memory 0x6000e8,load32 t.core.memory 0x600104,load32 t.core.memory 0x600108)

-- Original LIGHTDONE runs Light0, follows its zero timer to S_NULL, and RETs.
example : (E1M1PspriteLight.complete 3 (player 1)).map observation=
  some (0x12345678,0x603004,0,0,0) := by decide
-- Pistol and both shotgun entries preserve the original duration and intensity.
example : (E1M1PspriteLight.complete 2 (player 17)).map observation=
  some (0x12345678,0x603004,1,0x15c04,7) := by decide
example : (E1M1PspriteLight.complete 2 (player 30)).map observation=
  some (0x12345678,0x603004,1,0x15d70,4) := by decide
example : (E1M1PspriteLight.complete 2 (player 31)).map observation=
  some (0x12345678,0x603004,2,0x15d8c,3) := by decide
example : (E1M1PspriteLight.complete 1 (player 17)).isNone=true := by decide

def installation (timer next action : Word) : X86Memory.State :=
  ⟨write (write (write (write (fun _ => 0) 0 1) 3 0x600104) 4 0x603000) 6 0x600000,
    record (fun _ => 0) 1 timer next action⟩
example : (E1M1PspriteLight.advance (installation 1 0 0x2d490)).isNone=true := by decide
example : (E1M1PspriteLight.advance (installation 1 0 0x2d09a)).isNone=true := by decide
example : (E1M1PspriteLight.chain 3 ⟨installation 0 1 0x2db50,none,0x2d05e⟩).isNone=true := by decide
-- A light write overlapping the callback's return word cannot fake a return.
example : (E1M1PspriteLight.advance (put (installation 1 0 0x2db50) 6 (0x603000-236))).isNone=true := by decide

end PspriteLightChecks
