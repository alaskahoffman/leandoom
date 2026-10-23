import Doom.Proofs.E1M1PathMapSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapQuery
open Verification X86 X86Memory X86Control BlockSummary E1M1PathMap E1M1PathMapLookup

def traversal (s : X86Memory.State) := OriginalAimSetup.traversal (OriginalAimQuery.ray s).core

/-- Layout-only state for expressing future write addresses at query entry.
This does not model an executed instruction or assume future memory contents. -/
def withStack (s : X86Memory.State) (sp : Word) : X86Memory.State :=
  {s with regs := write s.regs 4 sp}

theorem ray_stack (s : X86Memory.State) : (OriginalAimQuery.ray s).core.regs 4=s.regs 4-(16#32) := by
  simp [OriginalAimQuery.ray,OriginalAimQuery.saved,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem traversal_stack (s : X86Memory.State) : (traversal s).core.regs 4=s.regs 4-(28#32) := by
  change (OriginalAimQuery.ray s).core.regs 4-(12#32)=_
  rw [ray_stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Query saves, aim-setup stores, and the subsequent traversal write footprint,
all expressed using the stack pointer before the ray prologue. -/
structure Safe (s : X86Memory.State) (a : Word) : Prop where
  saves : ∀ b∈OriginalAimQuery.saveWrites s, Apart a b
  setup : ∀ b∈(OriginalAimSetup.writes (withStack s (s.regs 4-(16#32)))).toList, Apart a b
  later : E1M1PathMapSetup.Safe (withStack s (s.regs 4-(28#32))) a

theorem setup_safe (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    ∀ b∈(OriginalAimSetup.writes (OriginalAimQuery.ray s).core).toList, Apart a b := by
  simpa only [OriginalAimSetup.writes,ray_stack,withStack,write,ite_true] using safe.setup

theorem traversal_safe (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    E1M1PathMapSetup.Safe (traversal s).core a := by
  simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,traversal_stack,withStack,write,ite_true] using safe.later

/-- The ray multiplies only registers after its four saves. The remaining aim
setup writes are handled by its existing frame theorem. -/
theorem traversal_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (traversal s).core.memory a=load32 s.memory a := by
  have setup := OriginalAimSetup.frame9 (OriginalAimQuery.ray s).core a (setup_safe s a safe)
  exact setup.trans (OriginalAimQuery.saved_frame s a safe.saves)

structure MapInputs (s : X86Memory.State) (base lines : Word) (words : Array Nat) (w h : Nat) : Prop where
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2^31
  heightBound : h<2^31
  table : load32 s.memory 0x2c100=base+(8#32)
  lists : load32 s.memory 0x2c10c=base
  lines : load32 s.memory 0x2c120=lines
  globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe s a
  image : WordImage s.memory base words
  imageSafe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))

theorem map_at_traversal (s : X86Memory.State) (base lines : Word) (words : Array Nat) (w h : Nat)
    (map : MapInputs s base lines words w h) :
    E1M1PathMapSetup.MapInputs (traversal s).core base lines words w h := by
  have keep (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    traversal_frame s a (map.globalsSafe a ha)
  refine ⟨(keep _ (by simp)).trans map.width,(keep _ (by simp)).trans map.height,map.widthBound,map.heightBound,
    (keep _ (by simp)).trans map.table,(keep _ (by simp)).trans map.lists,(keep _ (by simp)).trans map.lines,?_,?_,?_⟩
  · intro a ha
    exact traversal_safe s a (map.globalsSafe a ha)
  · intro i v hv
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
    have eq := congrArg (fun v : Word => v.extractLsb' 0 16) (traversal_frame s _ (map.imageSafe i hi))
    rw [SectorDispatch.load_half,SectorDispatch.load_half] at eq
    exact eq.trans (map.image i v hv)
  · intro i hi
    exact traversal_safe s _ (map.imageSafe i hi)

/-- Capacity is created later by initialization, so only later stack protection
is needed for the cursor; no initial cursor value is required. -/
theorem cursor_at_traversal (s : X86Memory.State)
    (safe : E1M1PathMapSetup.StackSafe (s.regs 4-(88#32)) (0x2c028#32)) :
    E1M1PathMapSetup.StackSafe ((traversal s).core.regs 4-(60#32)) (0x2c028#32) := by
  rw [traversal_stack]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe

/-- Origin words may use the same protected-read theorem; this supplies the map
origins at traversal entry without re-assuming their post-setup values. -/
theorem origins_at_traversal (s : X86Memory.State) (ox oy : Fixed)
    (x : load32 s.memory 0x2c104=ox.raw.toBitVec)
    (y : load32 s.memory 0x2c108=oy.raw.toBitVec)
    (safeX : Safe s (0x2c104#32)) (safeY : Safe s (0x2c108#32)) :
    load32 (traversal s).core.memory 0x2c104=ox.raw.toBitVec ∧
    load32 (traversal s).core.memory 0x2c108=oy.raw.toBitVec :=
  ⟨(traversal_frame s _ safeX).trans x,(traversal_frame s _ safeY).trans y⟩

/-- The same map contract works for any query entry, including either fallback
probe. This statement stops at the actual traversal CALL, before traversal runs. -/
theorem query_execution (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (words : Array Nat) (w h : Nat) (map : MapInputs s base lines words w h) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimSetup.program [] 36 ⟨s,f,0x2bb80⟩ (traversal s) ∧
    E1M1PathMapSetup.MapInputs (traversal s).core base lines words w h :=
  ⟨E1M1AimSetup.query_setup_execution s f,map_at_traversal s base lines words w h map⟩

/-- The first pistol/shotgun aim query now supplies the map contract needed by
all subsequent setup and the scan-entry join. Earlier firing preservation and
geometric/table encodings remain explicit obligations. -/
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : Cell) (w h : Nat)
    (map : MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words w h)
    (cursorSafe : E1M1PathMapSetup.StackSafe ((E1M1BulletAim.firstQuery gun s).core.regs 4-(88#32)) (0x2c028#32))
    (inside : Collision.pathCellInside (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w h=true)
    (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w]?=some c.offset) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core)) ∧
    ScanWords (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core lines c ∧
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core
      0x2ba20 (resolve lines) #[] c.ids.length :=
  E1M1PathMapSetup.first_scan_execution gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY
    base lines words c w h (map_at_traversal _ base lines words w h map)
    (cursor_at_traversal _ cursorSafe) inside valid selected
end Doom.Proofs.E1M1PathMapQuery
