import Doom.Proofs.E1M1PathMapQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapFiring
open Verification X86 X86Memory X86Control BlockSummary E1M1PathMap E1M1PathMapLookup

/-- Four saved registers plus the actual first geometry-query CALL. -/
theorem slope_stack (s : X86Memory.State) (f : Option Flags) :
    (OriginalBulletSlope.firstCall s f).core.regs 4=s.regs 4-(20#32) := by
  simp [OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

def slopeWrites (s : X86Memory.State) : List Word :=
  OriginalBulletSlope.saveWrites s ++ [s.regs 4-(20#32)]

theorem slope_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ b∈slopeWrites s, Apart a b) :
    load32 (OriginalBulletSlope.firstCall s f).core.memory a=load32 s.memory a := by
  have mem : (OriginalBulletSlope.firstCall s f).core.memory=
      store32 (OriginalBulletSlope.saved s).memory (s.regs 4-(20#32)) (0x2d7d5#32) := by
    simp [OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [mem,load_store_apart _ _ _ _ (safe _ (by simp [slopeWrites]))]
  exact OriginalBulletSlope.saved_frame s a (fun b hb => safe b (by simp [slopeWrites,hb]))

theorem flashed_stack (gun : Fire.Gun) (s : X86Memory.State) :
    (E1M1DischargeSetters.flashed gun s).core.regs 4=s.regs 4 := by
  change (E1M1DischargeSetters.flashCall gun s).core.regs 4+(4#32)=_
  simp only [E1M1DischargeSetters.flashCall,OriginalWeaponDischarge.flashCall,
    OriginalWeaponDischarge.debited,X86Routine.pushWord,put,write,ite_true,ite_false]
  rw [(E1M1DischargeSetters.posed_registers gun s).2]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem aim_stack (gun : Fire.Gun) (s : X86Memory.State) :
    (E1M1DischargeSetters.aimCall gun s).core.regs 4=s.regs 4-(4#32) := by
  change (E1M1DischargeSetters.flashed gun s).core.regs 4-(4#32)=_
  rw [flashed_stack]

theorem query_stack (gun : Fire.Gun) (s : X86Memory.State) :
    (E1M1BulletAim.firstQuery gun s).core.regs 4=s.regs 4-(24#32) := by
  rw [E1M1BulletAim.firstQuery,slope_stack,aim_stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Every destination is calculated from the initial state by the existing
setter/debit summaries. These are address-separation premises, not assumptions
that intervening calls returned a correct map image. -/
structure Safe (gun : Fire.Gun) (s : X86Memory.State) (a : Word) : Prop where
  beforeFlash : ∀ b∈E1M1DischargeSetters.beforeFlashWrites gun s, Apart a b
  flash : ∀ b∈E1M1FlashInstall.writes (E1M1DischargeSetters.flashCall gun s).core, Apart a b
  aim : Apart a (s.regs 4-(4#32))
  slope : ∀ b∈slopeWrites (E1M1DischargeSetters.aimCall gun s).core, Apart a b
  later : E1M1PathMapQuery.Safe (E1M1PathMapQuery.withStack s (s.regs 4-(24#32))) a

theorem query_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word) (safe : Safe gun s a) :
    load32 (E1M1BulletAim.firstQuery gun s).core.memory a=load32 s.memory a := by
  have first := slope_frame (E1M1DischargeSetters.aimCall gun s).core
    (E1M1DischargeSetters.aimCall gun s).flags a safe.slope
  have aim : load32 (E1M1DischargeSetters.aimCall gun s).core.memory a=
      load32 (E1M1DischargeSetters.flashed gun s).core.memory a := by
    change load32 (store32 (E1M1DischargeSetters.flashed gun s).core.memory
      ((E1M1DischargeSetters.flashed gun s).core.regs 4-(4#32)) _) a=_
    rw [flashed_stack]
    exact load_store_apart _ _ _ _ safe.aim
  exact first.trans (aim.trans ((E1M1FlashInstall.memory_frame gun _ a safe.flash).trans
    (E1M1DischargeSetters.before_flash_frame gun s a safe.beforeFlash)))

theorem query_safe (gun : Fire.Gun) (s : X86Memory.State) (a : Word) (safe : Safe gun s a) :
    E1M1PathMapQuery.Safe (E1M1BulletAim.firstQuery gun s).core a := by
  rcases safe.later with ⟨saves,setup,later⟩
  constructor
  · simpa only [OriginalAimQuery.saveWrites,query_stack,E1M1PathMapQuery.withStack,write,ite_true] using saves
  · simpa only [OriginalAimSetup.writes,query_stack,E1M1PathMapQuery.withStack,write,ite_true] using setup
  · simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,query_stack,
      E1M1PathMapQuery.withStack,write,ite_true] using later

structure MapInputs (gun : Fire.Gun) (s : X86Memory.State) (base lines : Word)
    (words : Array Nat) (w h : Nat) : Prop where
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2^31
  heightBound : h<2^31
  table : load32 s.memory 0x2c100=base+(8#32)
  lists : load32 s.memory 0x2c10c=base
  lines : load32 s.memory 0x2c120=lines
  globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe gun s a
  image : WordImage s.memory base words
  imageSafe : ∀ i<words.size, Safe gun s (base+BitVec.ofNat 32 (2*i))

theorem map_at_query (gun : Fire.Gun) (s : X86Memory.State) (base lines : Word)
    (words : Array Nat) (w h : Nat) (map : MapInputs gun s base lines words w h) :
    E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words w h := by
  have keep (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    query_frame gun s a (map.globalsSafe a ha)
  refine ⟨(keep _ (by simp)).trans map.width,(keep _ (by simp)).trans map.height,map.widthBound,map.heightBound,
    (keep _ (by simp)).trans map.table,(keep _ (by simp)).trans map.lists,(keep _ (by simp)).trans map.lines,?_,?_,?_⟩
  · intro a ha
    exact query_safe gun s a (map.globalsSafe a ha)
  · intro i v hv
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
    have eq := congrArg (fun v : Word => v.extractLsb' 0 16) (query_frame gun s _ (map.imageSafe i hi))
    rw [SectorDispatch.load_half,SectorDispatch.load_half] at eq
    exact eq.trans (map.image i v hv)
  · intro i hi
    exact query_safe gun s _ (map.imageSafe i hi)

theorem cursor_at_query (gun : Fire.Gun) (s : X86Memory.State)
    (safe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32)) :
    E1M1PathMapSetup.StackSafe ((E1M1BulletAim.firstQuery gun s).core.regs 4-(88#32)) (0x2c028#32) := by
  rw [query_stack]
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe

/-- Actual pose/debit/flash/light and bullet-slope calls, with protected map
state derived from their common post-sound entry. -/
theorem query_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (base lines : Word) (words : Array Nat) (w h : Nat) (map : MapInputs gun s base lines words w h) :
    (∃ n≤127, X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1BulletAim.firstQuery gun s)) ∧
    E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words w h :=
  ⟨E1M1BulletAim.first_query_execution gun s f weapon input,map_at_query gun s base lines words w h map⟩

/-- No intermediate map representation is assumed between post-sound firing
entry and the first scan header. Geometric/loader/earlier-sound obligations
remain distinct from this protected-memory connection. -/
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : Cell) (w h : Nat)
    (map : MapInputs gun s base lines words w h)
    (cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32))
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
  E1M1PathMapQuery.first_scan_execution gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY
    base lines words c w h (map_at_query gun s base lines words w h map)
    (cursor_at_query gun s cursorSafe) inside valid selected
end Doom.Proofs.E1M1PathMapFiring
