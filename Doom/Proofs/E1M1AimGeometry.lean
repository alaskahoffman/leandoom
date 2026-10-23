import Doom.Proofs.E1M1PathMapFiring
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimGeometry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMapQuery (withStack traversal)

/-- Only the two selected table entries are read by one ray. Their values are
related to the production tables; no endpoint result is assumed. -/
structure RaySamples (s : X86Memory.State) (angle : Angle) (distance : Fixed) : Prop where
  angleReg : s.regs 2=angle.raw.toBitVec
  rangeReg : s.regs 3=distance.raw.toBitVec
  pointer : load32 s.memory 0x13584=0x7a84
  cosine : load32 s.memory ((angle.raw.toBitVec >>> 19 <<< 2)+0x7a84)=angle.fineCosine.raw.toBitVec
  sine : load32 s.memory ((angle.raw.toBitVec >>> 19 <<< 2)+0x5a84)=angle.fineSine.raw.toBitVec
  safe : ∀ a∈[(0x13584#32),(angle.raw.toBitVec >>> 19 <<< 2)+0x7a84,
    (angle.raw.toBitVec >>> 19 <<< 2)+0x5a84], ∀ b∈OriginalAimQuery.saveWrites s, Apart a b

theorem samples_of_tables (s : X86Memory.State) (angle : Angle) (distance : Fixed)
    (h : OriginalAimQuery.RayInputs s angle distance) : RaySamples s angle distance := by
  have samples := thrust_selected_tables s.memory angle h.tables
  rw [h.tables.cosinePointer] at samples
  exact ⟨h.angleReg,h.rangeReg,h.tables.cosinePointer,samples.1,samples.2,h.tableSafe⟩

theorem selected_samples (s : X86Memory.State) (angle : Angle) (distance : Fixed)
    (h : RaySamples s angle distance) :
    OriginalAimQuery.cosine s=angle.fineCosine.raw.toBitVec ∧
    OriginalAimQuery.sine s=angle.fineSine.raw.toBitVec := by
  have ptr : OriginalAimQuery.cosinePointer s=0x7a84 := by
    rw [OriginalAimQuery.cosinePointer,OriginalAimQuery.saved_frame s _ (h.safe _ (by simp)),h.pointer]
  constructor
  · unfold OriginalAimQuery.cosine
    rw [ptr]
    simp only [OriginalAimQuery.index,h.angleReg]
    rw [BitVec.add_comm,OriginalAimQuery.saved_frame s _ (h.safe _ (by simp)),h.cosine]
  · unfold OriginalAimQuery.sine
    simp only [OriginalAimQuery.index,h.angleReg]
    rw [OriginalAimQuery.saved_frame s _ (h.safe _ (by simp)),h.sine]

theorem endpoint (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : RaySamples s angle distance) :
    (thing.x.raw.toBitVec+(OriginalAimQuery.ray s).core.regs 1,
     thing.y.raw.toBitVec+(OriginalAimQuery.ray s).core.regs 6)=
    ((thing.attackEndpoint angle distance).1.raw.toBitVec,
     (thing.attackEndpoint angle distance).2.raw.toBitVec) := by
  have tab := selected_samples s angle distance h
  change (thing.x.raw.toBitVec+OriginalAimQuery.cosine s*OriginalAimQuery.units s,
    thing.y.raw.toBitVec+OriginalAimQuery.units s*OriginalAimQuery.sine s)=_
  rw [tab.1,tab.2]
  apply Prod.ext
  · change thing.x.raw.toBitVec+angle.fineCosine.raw.toBitVec*(s.regs 3).sshiftRight 16 =
      thing.x.raw.toBitVec+distance.raw.toBitVec.sshiftRight 16*angle.fineCosine.raw.toBitVec
    rw [h.rangeReg,BitVec.mul_comm]
  · change thing.y.raw.toBitVec+(s.regs 3).sshiftRight 16*angle.fineSine.raw.toBitVec =
      thing.y.raw.toBitVec+distance.raw.toBitVec.sshiftRight 16*angle.fineSine.raw.toBitVec
    rw [h.rangeReg]

theorem ray_registers (s : X86Memory.State) :
    (OriginalAimQuery.ray s).core.regs 0=s.regs 0 ∧
    (OriginalAimQuery.ray s).core.regs 3=s.regs 3 := by
  simp [OriginalAimQuery.ray,OriginalAimQuery.saved,X86Routine.pushWord,put,write]

theorem ray_frame (s : X86Memory.State) (a : Word) (h : E1M1PathMapQuery.Safe s a) :
    load32 (OriginalAimQuery.ray s).core.memory a=load32 s.memory a :=
  OriginalAimQuery.saved_frame s a h.saves

/-- Shooter words, selected trigonometric samples, map origins and layout are
all stated before the ray prologue. Layout-only states carry no memory premise. -/
structure Inputs (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance ox oy : Fixed) : Prop where
  ray : RaySamples s angle distance
  x : load32 s.memory (s.regs 0+12)=thing.x.raw.toBitVec
  y : load32 s.memory (s.regs 0+16)=thing.y.raw.toBitVec
  z : load32 s.memory (s.regs 0+20)=thing.z.raw.toBitVec
  height : load32 s.memory (s.regs 0+68)=thing.height.raw.toBitVec
  actorSafe : ∀ a∈OriginalAimSetup.actorReads s, E1M1PathMapQuery.Safe s a
  originX : load32 s.memory 0x2c104=ox.raw.toBitVec
  originY : load32 s.memory 0x2c108=oy.raw.toBitVec
  safeX : E1M1PathMapQuery.Safe s (0x2c104#32)
  safeY : E1M1PathMapQuery.Safe s (0x2c108#32)
  aimLayout : OriginalAimSetup.Separated (withStack s (s.regs 4-(16#32)))
  flagSafe : ∀ b∈(OriginalPathInit.writes (withStack s (s.regs 4-(28#32)))).toList,
    Apart (s.regs 4-(24#32)) b
  pathLayout : OriginalPathInit.Separated (withStack s (s.regs 4-(28#32)))

theorem setup_inputs (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance ox oy : Fixed) (h : Inputs s thing angle distance ox oy) :
    OriginalAimSetup.Inputs (OriginalAimQuery.ray s).core thing angle distance := by
  have regs := ray_registers s
  have keep (a : Word) (ha : a∈OriginalAimSetup.actorReads s) := ray_frame s a (h.actorSafe a ha)
  refine ⟨?_,?_,?_,?_,regs.2.trans h.ray.rangeReg,endpoint s thing angle distance h.ray,?_,?_⟩
  · rw [regs.1,keep _ (by simp [OriginalAimSetup.actorReads]),h.x]
  · rw [regs.1,keep _ (by simp [OriginalAimSetup.actorReads]),h.y]
  · rw [regs.1,keep _ (by simp [OriginalAimSetup.actorReads]),h.z]
  · rw [regs.1,keep _ (by simp [OriginalAimSetup.actorReads]),h.height]
  · intro a ha
    simp only [OriginalAimSetup.actorReads,regs.1] at ha
    exact E1M1PathMapQuery.setup_safe s a (h.actorSafe a ha)
  · simpa only [OriginalAimSetup.Separated,OriginalAimSetup.writes,
      E1M1PathMapQuery.ray_stack,withStack,write,ite_true] using h.aimLayout

theorem path_inputs (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance ox oy : Fixed) (h : Inputs s thing angle distance ox oy) :
    OriginalPathInit.Inputs (traversal s).core ox oy thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 := by
  have origins := E1M1PathMapQuery.origins_at_traversal s ox oy h.originX h.originY h.safeX h.safeY
  have sp : (OriginalAimSetup.traversal (OriginalAimQuery.ray s).core).core.regs 4=s.regs 4-(28#32) :=
    E1M1PathMapQuery.traversal_stack s
  apply E1M1PathInit.inputs_from_setup _ thing angle distance ox oy
    (setup_inputs s thing angle distance ox oy h) origins.1 origins.2
  · intro a ha
    simp only [OriginalPathInit.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    · exact (E1M1PathMapQuery.traversal_safe s _ h.safeX).1
    · exact (E1M1PathMapQuery.traversal_safe s _ h.safeY).1
    · simpa [OriginalPathInit.writes,sp,
        withStack,write,ite_true,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.flagSafe
  · simpa only [OriginalPathInit.Separated,OriginalPathInit.writes,
      sp,withStack,write,ite_true] using h.pathLayout

theorem query_path_correspondence (s : X86Memory.State) (f : Option Flags)
    (thing : Collision.SolidThing) (angle : Angle) (distance ox oy : Fixed)
    (h : Inputs s thing angle distance ox oy) :
    ∃ n, n≤96 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathInit.program [] n ⟨s,f,0x2bb80⟩
      (OriginalPathInit.result (traversal s).core) ∧
    OriginalPathInit.Ready (traversal s).core (OriginalPathInit.result (traversal s).core)
      (Collision.pathStart ox oy thing.x thing.y
        (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2) := by
  obtain ⟨n,hn,path⟩ := E1M1PathInit.query_path_execution s f
  exact ⟨n,hn,path,OriginalPathInit.ready _ ox oy _ _ _ _ (path_inputs s thing angle distance ox oy h)⟩
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) ox oy)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : E1M1PathMap.Cell) (w h : Nat)
    (map : E1M1PathMapFiring.MapInputs gun s base lines words w h)
    (cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32))
    (inside : Collision.pathCellInside (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockX
      (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockY w h=true)
    (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockX
      (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockY w]?=some c.offset) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core)) ∧
    E1M1PathMapLookup.ScanWords (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core lines c ∧
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core
      0x2ba20 (E1M1PathMap.resolve lines) #[] c.ids.length := by
  exact E1M1PathMapFiring.first_scan_execution gun s f weapon input ox oy thing.x thing.y
    (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2
    (path_inputs _ thing angle _ ox oy geometry) (setup_inputs _ thing angle _ ox oy geometry).separated
    xout yout okX okY base lines words c w h map cursorSafe inside valid selected
end Doom.Proofs.E1M1AimGeometry
