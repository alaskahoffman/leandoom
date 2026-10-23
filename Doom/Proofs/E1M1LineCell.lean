import Doom.Proofs.E1M1PathCell
import Doom.Proofs.OriginalLineCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LineCell
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathCell.program pc with
  | some op => some op
  | none => OriginalLineCell.program pc

theorem contains_prior (pc : Nat) (h : E1M1PathCell.program pc≠none) :
    program pc=E1M1PathCell.program pc := by
  unfold program
  cases hp : E1M1PathCell.program pc <;> simp_all

theorem contains_cell (pc : Nat) (h : OriginalLineCell.program pc≠none) :
    program pc=OriginalLineCell.program pc := by
  have range : 0x2c541≤pc ∧ pc<0x2c587 := by
    by_cases r : 0x2c541≤pc ∧ pc<0x2c587
    · exact r
    · simp [OriginalLineCell.program,OriginalLineCell.bytesProgram,r] at h
  have all : ∀ i : Fin 70, program (0x2c541+i.val)=OriginalLineCell.program (0x2c541+i.val) := by decide
  have eq : 0x2c541+(pc-0x2c541)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c541,by omega⟩

/-- Outside cells already returned. Inside cells proceed to the first list item. -/
def continueCell (s : X86Control.State) : X86Control.State :=
  if s.pc=0x2c541 then OriginalLineCell.first s.core else s

theorem continue_execution (s : X86Control.State) :
    ∃ n, n≤19 ∧ X86Routine.Prefix program [] n s (continueCell s) := by
  by_cases h : s.pc=0x2c541
  · obtain ⟨n,hn,path⟩ := OriginalLineCell.first_execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ h] at path
    exact ⟨n,hn,by simpa only [continueCell,if_pos h] using path.transfer program [] contains_cell (by simp)⟩
  · exact ⟨0,by omega,by simpa only [continueCell,if_neg h] using X86Routine.Prefix.nil (program:=program) (exits:=[]) s⟩

def firstCell (gun : Fire.Gun) (s : X86Memory.State) := continueCell (E1M1PathCell.firstBounds gun s)

/-- Continuous original firing reaches an outside-cell return, the list sentinel,
a skipped duplicate's next item, or the actual new-line callback entry. -/
theorem first_cell_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤379 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstCell gun s) := by
  obtain ⟨n,hn,a,_⟩ := E1M1PathCell.first_bounds_execution gun s f c h
    ox oy sx sy ex ey geometry layout xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := continue_execution (E1M1PathCell.firstBounds gun s)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (X86CodeMemory.lift_success b FloorCaller.cm)⟩

/-- Map representation at iterator entry, before its stack writes. Word-sized
separation at the halfword read is conservative and explicit. -/
structure MapData (s : X86Memory.State) (x y : Int32) (w off : Nat) (table lists : Word) : Prop where
  tableGlobal : load32 s.memory 0x2c100=table
  listGlobal : load32 s.memory 0x2c10c=lists
  offsetWord : load16 s.memory (table+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 1))=BitVec.ofNat 16 off
  offsetBound : off<32768
  safe : ∀ a∈[(0x2c100#32),0x2c10c,table+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 1)],
    Apart a (s.regs 4-4) ∧ Apart a (s.regs 4-8)

theorem inside_state (s : X86Memory.State) (h : OriginalLineBounds.Inside (OriginalLineBounds.entry s)) :
    OriginalLineBounds.result s=
      ⟨OriginalLineBounds.loaded (OriginalLineBounds.entry s),
       some (compare32 ((OriginalLineBounds.entry s).regs 2) (OriginalLineBounds.height (OriginalLineBounds.entry s))),0x2c541⟩ := by
  rcases h with ⟨hx,hy,hw,hh⟩
  simp [OriginalLineBounds.result,OriginalLineBounds.Inside,OriginalLineBounds.guarded,hx,hy,hw,hh,
    show ¬((OriginalLineBounds.entry s).regs 0).toInt < 0 by omega,
    show ¬((OriginalLineBounds.entry s).regs 2).toInt < 0 by omega,
    show ¬(OriginalLineBounds.width (OriginalLineBounds.entry s)).toInt≤((OriginalLineBounds.entry s).regs 0).toInt by omega,
    show ¬(OriginalLineBounds.height (OriginalLineBounds.entry s)).toInt≤((OriginalLineBounds.entry s).regs 2).toInt by omega]

/-- Bounds, coordinates, width and map reads are transported from the iterator
entry; they are not assumed again at the interior lookup PC. -/
theorem bounds_to_lookup (s : X86Memory.State) (x y : Int32) (w h off : Nat) (table lists : Word)
    (bounds : OriginalLineBounds.Inputs s x y w h)
    (inside : Collision.pathCellInside x y w h=true)
    (map : MapData s x y w off table lists) :
    OriginalLineCell.Inputs (OriginalLineBounds.result s).core x y w off table lists := by
  have ins := (OriginalLineBounds.live_bounds s x y w h bounds).mpr inside
  have keep (a : Word) (ha : a∈[(0x2c100#32),0x2c10c,table+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 1)]) :=
    OriginalLineBounds.entry_frame s a (map.safe a ha).1 (map.safe a ha).2
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) (keep (table+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 1)) (by simp))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  have ew := OriginalLineBounds.entry_frame s (0x2c0fc#32) (bounds.safe _ (by simp)).1 (bounds.safe _ (by simp)).2
  have nonneg : 0≤x.toInt ∧ 0≤y.toInt := by
    simp only [Collision.pathCellInside,Bool.and_eq_true,decide_eq_true_eq] at inside
    exact ⟨inside.1.1.1,inside.1.1.2⟩
  rw [inside_state s ins]
  constructor
  · exact nonneg.1
  · exact nonneg.2
  · simpa [OriginalLineBounds.loaded,put,write,(OriginalLineBounds.entry_coordinates s).1] using bounds.mapX
  · simpa [OriginalLineBounds.loaded,put,write,(OriginalLineBounds.entry_coordinates s).2.1] using bounds.mapY
  · simpa [OriginalLineBounds.loaded,OriginalLineBounds.width,put,write,ew] using bounds.width
  · change load32 (OriginalLineBounds.entry s).memory 0x2c100=table
    rw [keep _ (by simp),map.tableGlobal]
  · change load32 (OriginalLineBounds.entry s).memory 0x2c10c=lists
    rw [keep _ (by simp),map.listGlobal]
  · exact half.trans map.offsetWord
  · exact map.offsetBound

end Doom.Proofs.E1M1LineCell
