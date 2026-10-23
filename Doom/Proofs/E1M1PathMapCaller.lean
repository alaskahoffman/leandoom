import Doom.Proofs.E1M1PathMapBounds
import Doom.Proofs.E1M1PathCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapCaller
open Verification X86 X86Memory X86Control BlockSummary E1M1PathMap E1M1PathMapLookup

def bytesProgram (dispatch entry ret cell : List UInt8) : X86Routine.Program := fun pc =>
  match OriginalPathCell.bytesProgram dispatch pc with
  | some op => some op
  | none => E1M1PathMapBounds.bytesProgram entry ret cell pc

def program := bytesProgram OriginalPathCell.code OriginalLineBounds.lineEntry
  OriginalLineBounds.lineReturn OriginalLineCell.code

theorem contains_dispatch (pc : Nat) (h : OriginalPathCell.program pc≠none) :
    program pc=OriginalPathCell.program pc := by
  unfold program bytesProgram
  change (match OriginalPathCell.program pc with | some op => some op | none => _) = _
  cases hp : OriginalPathCell.program pc <;> simp_all

theorem contains_bounds (pc : Nat) (h : E1M1PathMapBounds.program pc≠none) :
    program pc=E1M1PathMapBounds.program pc := by
  by_cases hr : 0x2ca7f≤pc ∧ pc<0x2cab5
  · have a : ¬(0x2c520≤pc ∧ pc<0x2c541) := by omega
    have b : ¬(0x2c587≤pc ∧ pc<0x2c591) := by omega
    have c : ¬(0x2c541≤pc ∧ pc<0x2c587) := by omega
    simp [E1M1PathMapBounds.program,E1M1PathMapBounds.bytesProgram,
      OriginalLineBounds.bytesProgram,OriginalLineCell.bytesProgram,a,b,c] at h
  · simp [program,bytesProgram,OriginalPathCell.bytesProgram,hr,E1M1PathMapBounds.program]

def call (s : X86Memory.State) := OriginalPathCell.called true s (OriginalPathCell.gateFlags true s)
def scan (s : X86Memory.State) := E1M1PathMapBounds.scanStart (call s).core
def returned (s : X86Memory.State) := OriginalLineBounds.result (call s).core
def resumed (s : X86Memory.State) := OriginalPathCell.resumed true (returned s).core

theorem call_stack (s : X86Memory.State) : (call s).core.regs 4=s.regs 4-(4#32) :=
  (OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)).2.2.2.1

theorem call_return (s : X86Memory.State) :
    load32 (call s).core.memory (s.regs 4-(4#32))=(0x2ca94#32) :=
  (OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)).2.2.2.2.1

theorem call_frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4-(4#32))) :
    load32 (call s).core.memory a=load32 s.memory a :=
  OriginalPathCell.call_frame true s (OriginalPathCell.gateFlags true s) a safe

/-- Protect against the CALL return word and both iterator prologue stores. -/
def Safe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (s.regs 4-(4#32)) ∧ Apart a (s.regs 4-(8#32)) ∧ Apart a (s.regs 4-(12#32))

theorem safe_at_call (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    E1M1PathMapBounds.Safe (call s).core a := by
  have sp := call_stack s
  unfold E1M1PathMapBounds.Safe
  change Apart a ((call s).core.regs 4-(4#32)) ∧ Apart a ((call s).core.regs 4-(8#32))
  rw [sp]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2

structure Dimensions (s : X86Memory.State) (w h : Nat) : Prop where
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2^31
  heightBound : h<2^31
  safe : ∀ a∈[(0x2c0fc#32),0x2c110], Safe s a

/-- Coordinates are taken from the actual grid registers and copied by CALL setup. -/
theorem bounds_inputs (s : X86Memory.State) (x y : Int32) (w h : Nat)
    (dims : Dimensions s w h) (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec) :
    OriginalLineBounds.Inputs (call s).core x y w h := by
  have args := OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)
  refine ⟨args.1.trans mapX,args.2.1.trans mapY,?_,?_,dims.widthBound,dims.heightBound,?_⟩
  · exact (call_frame s _ (dims.safe _ (by simp)).1).trans dims.width
  · exact (call_frame s _ (dims.safe _ (by simp)).1).trans dims.height
  · intro a ha
    exact safe_at_call s a (dims.safe a ha)

structure Globals (s : X86Memory.State) (base lines : Word) : Prop where
  table : load32 s.memory 0x2c100=base+(8#32)
  lists : load32 s.memory 0x2c10c=base
  lines : load32 s.memory 0x2c120=lines
  safe : ∀ a∈[(0x2c100#32),0x2c10c,0x2c120], Safe s a

theorem globals_at_call (s : X86Memory.State) (base lines : Word) (globals : Globals s base lines) :
    E1M1PathMapBounds.Globals (call s).core base lines := by
  refine ⟨?_,?_,?_,fun a ha => safe_at_call s a (globals.safe a ha)⟩
  · exact (call_frame s _ (globals.safe _ (by simp)).1).trans globals.table
  · exact (call_frame s _ (globals.safe _ (by simp)).1).trans globals.lists
  · exact (call_frame s _ (globals.safe _ (by simp)).1).trans globals.lines

def ImageSafe (s : X86Memory.State) (base : Word) (words : Array Nat) : Prop :=
  ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))

theorem image_at_call (s : X86Memory.State) (base : Word) (words : Array Nat)
    (image : WordImage s.memory base words) (safe : ImageSafe s base words) :
    WordImage (call s).core.memory base words ∧ E1M1PathMapBounds.ImageSafe (call s).core base words := by
  constructor
  · intro i value h
    obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp h
    have keep := congrArg (fun v : Word => v.extractLsb' 0 16)
      (OriginalPathCell.call_frame true s (OriginalPathCell.gateFlags true s) _ (safe i bound).1)
    rw [SectorDispatch.load_half,SectorDispatch.load_half] at keep
    exact keep.trans (image i value h)
  · intro i hi
    exact safe_at_call s _ (safe i hi)

theorem enter_execution (s : X86Memory.State) (f : Option Flags)
    (enabled : OriginalPathCell.enabled true s=true) :
    ∃ n≤6, X86Routine.Prefix program [] n ⟨s,f,0x2ca7f⟩ (call s) := by
  obtain ⟨n,hn,path⟩ := OriginalPathCell.enter_execution true s f
  simp only [OriginalPathCell.enter,enabled,↓reduceIte] at path
  exact ⟨n,hn,path.transfer program [] contains_dispatch (by simp)⟩

/-- The real caller establishes iterator arguments, return word, callback and map
representation before the joined bounds/lookup execution. -/
theorem inside_to_scan (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (words : Array Nat) (c : Cell) (x y : Int32) (w h : Nat)
    (enabled : OriginalPathCell.enabled true s=true) (dims : Dimensions s w h)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (globals : Globals s base lines) (inside : Collision.pathCellInside x y w h=true)
    (valid : c.Valid words) (image : WordImage s.memory base words) (safe : ImageSafe s base words)
    (selected : words[4+Collision.pathCellIndex x y w]?=some c.offset) :
    (∃ n≤30, X86Routine.Prefix program [] n ⟨s,f,0x2ca7f⟩ (scan s)) ∧
    ScanWords (scan s).core lines c ∧ (scan s).pc=0x2c57f ∧
    (scan s).core.regs 4=s.regs 4-(12#32) := by
  have retained := image_at_call s base words image safe
  obtain ⟨⟨m,hm,b⟩,items,pc,sp⟩ := E1M1PathMapBounds.inside_to_scan (call s).core (call s).flags
    base lines words c x y w h (bounds_inputs s x y w h dims mapX mapY)
    (globals_at_call s base lines globals) inside valid retained.1 retained.2 selected
  obtain ⟨n,hn,a⟩ := enter_execution s f enabled
  have b := b.transfer program [] contains_bounds (by simp)
  have callPC : (call s).pc=0x2c520 := rfl
  rw [OriginalPathXStep.at_pc _ _ callPC] at b
  refine ⟨⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩,items,pc,?_⟩
  have callSP := call_stack s
  change (scan s).core.regs 4=(call s).core.regs 4-(8#32) at sp
  rw [sp,callSP]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- An outside cell returns to the actual caller and passes its success test,
restoring the caller SP. No map image or callback result is assumed. -/
theorem outside_to_things (s : X86Memory.State) (f : Option Flags) (x y : Int32) (w h : Nat)
    (enabled : OriginalPathCell.enabled true s=true) (dims : Dimensions s w h)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (outside : Collision.pathCellInside x y w h=false) :
    (∃ n≤24, X86Routine.Prefix program [] n ⟨s,f,0x2ca7f⟩ (resumed s)) ∧
    (resumed s).pc=0x2ca9c ∧ (resumed s).core.regs 4=s.regs 4 ∧
    (resumed s).core.regs 0=1 := by
  obtain ⟨⟨m,hm,b⟩,value,sp,pc⟩ := E1M1PathMapBounds.outside_returns (call s).core (call s).flags
    x y w h (bounds_inputs s x y w h dims mapX mapY) outside
  have args := OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)
  have returnPC : (returned s).pc=0x2ca94 := by
    change (returned s).pc=_ at pc
    rw [pc,call_stack,call_return]
    rfl
  obtain ⟨n,hn,a⟩ := enter_execution s f enabled
  have b := b.transfer program [] contains_bounds (by simp)
  have callPC : (call s).pc=0x2c520 := rfl
  rw [OriginalPathXStep.at_pc _ _ callPC] at b
  have tail := (OriginalPathCell.resume_execution true (returned s).core (returned s).flags).transfer
    program [] contains_dispatch (by simp)
  change X86Routine.Prefix program [] 2 ⟨_,_,0x2ca94⟩ (resumed s) at tail
  rw [OriginalPathXStep.at_pc _ _ returnPC] at tail
  refine ⟨⟨n+m+2,by omega,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join a b) tail⟩,?_,?_,value⟩
  · change (if (returned s).core.regs 0=0 then 0x2cb0b else 0x2ca9c)=_
    change (returned s).core.regs 0=1 at value
    rw [value]; decide
  · change (returned s).core.regs 4=_
    change (returned s).core.regs 4=(call s).core.regs 4+(4#32) at sp
    rw [sp,call_stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- The extra CALL store preserves existing intercepts too; no new reserve is
required or manufactured across this whole caller-to-scan prefix. -/
theorem collection_preserved (s : X86Memory.State) (base : Word)
    (resolver : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolver hits reserve)
    (cursorSafe : Safe s (0x2c028#32))
    (recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8], Safe s (base+BitVec.ofNat 32 (12*i)+off)) :
    OriginalLineCollection.Tracks (scan s).core base resolver hits reserve := by
  apply E1M1PathMapBounds.collection_preserved
  · refine ⟨?_,?_,tracked.room⟩
    · intro i hi
      obtain ⟨frac,line,ptr⟩ := tracked.encoded i hi
      unfold OriginalLineFinish.RecordAt
      rw [call_frame s _ (by simpa only [BitVec.add_zero] using (recordsSafe i hi (0#32) (by simp)).1),
        call_frame s _ (recordsSafe i hi (4#32) (by simp)).1,
        call_frame s _ (recordsSafe i hi (8#32) (by simp)).1]
      exact ⟨frac,line,ptr⟩
    · change load32 (call s).core.memory (0x2c028#32)=_
      rw [call_frame s _ cursorSafe.1]
      exact tracked.cursor
  · exact safe_at_call s _ cursorSafe
  · intro i hi off ho
    exact safe_at_call s _ (recordsSafe i hi off ho)
/-- Extend the existing firing/grid program with the iterator caller and lookup. -/
def firingProgram (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathGridSetup.program pc with
  | some op => some op
  | none => program pc

theorem contains_grid (pc : Nat) (h : E1M1PathGridSetup.program pc≠none) :
    firingProgram pc=E1M1PathGridSetup.program pc := by
  unfold firingProgram
  cases hp : E1M1PathGridSetup.program pc <;> simp_all

theorem contains_caller (pc : Nat) (h : program pc≠none) :
    firingProgram pc=program pc := by
  by_cases r : 0x2ca7f≤pc ∧ pc<0x2cab5
  · have all : ∀ i : Fin 54, firingProgram (0x2ca7f+i.val)=program (0x2ca7f+i.val) := by decide +kernel
    have eq : 0x2ca7f+(pc-0x2ca7f)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2ca7f,by omega⟩
  · have range : 0x2c520≤pc ∧ pc<0x2c591 := by
      by_cases hr : 0x2c520≤pc ∧ pc<0x2c591
      · exact hr
      · have a : ¬(0x2c520≤pc ∧ pc<0x2c541) := by omega
        have b : ¬(0x2c587≤pc ∧ pc<0x2c591) := by omega
        have c : ¬(0x2c541≤pc ∧ pc<0x2c587) := by omega
        simp [program,bytesProgram,OriginalPathCell.bytesProgram,r,E1M1PathMapBounds.bytesProgram,
          OriginalLineBounds.bytesProgram,OriginalLineCell.bytesProgram,a,b,c] at h
    have all : ∀ i : Fin 113, firingProgram (0x2c520+i.val)=program (0x2c520+i.val) := by decide +kernel
    have eq : 0x2c520+(pc-0x2c520)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c520,by omega⟩

/-- Reuse the same connection for pistol and shotgun. The original firing prefix
now reaches scan entry; map facts remain explicit at the first grid state, while
coordinates and traversal-enable flags are derived from the preceding code. -/
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : Cell) (w h : Nat)
    (dims : Dimensions (E1M1PathGridSetup.firstGrid gun s).core w h)
    (globals : Globals (E1M1PathGridSetup.firstGrid gun s).core base lines)
    (inside : Collision.pathCellInside (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w h=true)
    (valid : c.Valid words)
    (image : WordImage (E1M1PathGridSetup.firstGrid gun s).core.memory base words)
    (safe : ImageSafe (E1M1PathGridSetup.firstGrid gun s).core base words)
    (selected : words[4+Collision.pathCellIndex (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w]?=some c.offset) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (scan (E1M1PathGridSetup.firstGrid gun s).core)) ∧
    ScanWords (scan (E1M1PathGridSetup.firstGrid gun s).core).core lines c := by
  obtain ⟨n,hn,a,ready⟩ := E1M1PathGridSetup.first_grid_correspondence gun s f weapon input
    ox oy sx sy ex ey geometry xout yout okX okY
  have flag := E1M1PathCell.first_flags_from_caller gun s ox oy sx sy ex ey geometry layout
  obtain ⟨⟨m,hm,b⟩,items,_⟩ := inside_to_scan (E1M1PathGridSetup.firstGrid gun s).core
    (E1M1PathGridSetup.firstGrid gun s).flags base lines words c _ _ w h flag dims ready.mapX ready.mapY
    globals inside valid image safe selected
  have a := a.transfer firingProgram [] contains_grid (by simp)
  have b := X86CodeMemory.lift_success (b.transfer firingProgram [] contains_caller (by simp)) FloorCaller.cm
  rw [OriginalPathXStep.at_pc _ _ ready.pc] at b
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩,items⟩
end Doom.Proofs.E1M1PathMapCaller
