import Doom.Proofs.E1M1PspriteChain
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
namespace PspriteChainChecks

def machine (timer next action : Word) : X86Memory.State :=
  ⟨write (write (write (fun _ => 0) 0 1) 3 0x600100) 4 0x603000,
    store32 (store32 (store32 (fun _ => 0) (0x15a28+28+8) timer)
      (0x15a28+28+16) next) (0x15a28+28+12) action⟩

def start (timer next action : Word) : X86Control.State :=
  ⟨machine timer next action,none,0x2d05e⟩

-- Exhaustion is failure, including when already at an epilogue.
example : (E1M1PspriteChain.chain 0 (start 1 0 0)).isNone=true := rfl
example : (E1M1PspriteChain.chain 0 {start 1 0 0 with pc := 0x2d0ac}).isNone=true := rfl
-- One installation needs fuel for the subsequent terminal branch too.
example : (E1M1PspriteChain.chain 1 (start 1 0 0)).isNone=true := by decide
example : ((E1M1PspriteChain.chain 2 (start 1 0 0)).map fun t =>
  (t.pc,t.core.regs 4,load32 t.core.memory 0x600100,load32 t.core.memory 0x600104))=
  some (0,0x60300c,0x15a44,1) := by decide
-- Zero-tic S_NULL actually clears the state pointer before returning.
example : ((E1M1PspriteChain.chain 2 (start 0 0 0)).map fun t =>
  (t.pc,t.core.regs 4,load32 t.core.memory 0x600100))=some (0,0x60300c,0) := by decide
-- A self-loop never becomes a successful return just because fuel runs out.
example : (E1M1PspriteChain.chain 4 (start 0 1 0)).isNone=true := by decide
-- A callback equal to the no-action continuation PC is still an action.
example : (E1M1PspriteChain.chain 3 (start 1 0 0x2d09a)).isNone=true := by decide
example : (E1M1PspriteChain.chain 3 (start 0 0 0x2d490)).isNone=true := by decide
example : (E1M1PspriteChain.chain 3 {start 1 0 0 with pc := 0x2d088}).isNone=true := by decide

end PspriteChainChecks
