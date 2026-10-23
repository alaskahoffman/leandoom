import Doom.Proofs.E1M1PathAdvance
import Doom.Proofs.E1M1ThingListFrame
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringAdvance
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)

def program : X86Routine.Program := fun pc =>
  match E1M1FiringCellReturn.program pc with
  | some op => some op
  | none => OriginalPathAdvance.program pc

theorem contains_prior (pc : Nat) (h : E1M1FiringCellReturn.program pc≠none) :
    program pc=E1M1FiringCellReturn.program pc := by
  unfold program
  cases eq : E1M1FiringCellReturn.program pc <;> simp_all

theorem contains_advance (pc : Nat) (h : OriginalPathAdvance.program pc≠none) :
    program pc=OriginalPathAdvance.program pc := by
  have range : 0x2cab5≤pc ∧ pc<0x2cafd := by
    by_cases r : 0x2cab5≤pc ∧ pc<0x2cafd
    · exact r
    · simp [OriginalPathAdvance.program,OriginalPathAdvance.bytesProgram,r] at h
  have all : ∀ i : Fin 72, program (0x2cab5+i.val)=OriginalPathAdvance.program (0x2cab5+i.val) := by decide
  have eq : 0x2cab5+(pc-0x2cab5)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2cab5,by omega⟩

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input
attribute [local irreducible] Collision.SolidThing.attackEndpoint
variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links : Word) (nodes : List E1M1ThingList.Node)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=E1M1ThingList.head nodes)
include returns flag lookupSafe global selected

variable (objects : Nat → Word)
    (d : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nodes)
include d


def result := OriginalPathAdvance.result (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core

/-- Continuous machine execution includes the first cell's advancement. The
numeric transition is stated relative to the reached observation: connecting
its remaining intercept/stride/end/counter values to initialization is still
required before this becomes full production grid-walk correspondence. -/
theorem execution (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) (f : Option Flags) :
    let before := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    (∃ steps≤427+281*c.ids.length+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe before.core) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe before.core) := by
  obtain ⟨⟨n,hn,prior⟩,_,sp,pc,_,_,_⟩ := E1M1FiringCellReturn.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene f
  let before := E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
  obtain ⟨⟨m,hm,tail⟩,numeric,next,stack⟩ := E1M1PathAdvance.execution before.core before.flags
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans
    (prior.transfer program [] contains_prior (by simp))
    (X86CodeMemory.lift_success (tail.transfer program [] contains_advance (by simp)) FloorCaller.cm)⟩,
    stack.trans sp,numeric,next⟩
end Firing
end Doom.Proofs.E1M1FiringAdvance
