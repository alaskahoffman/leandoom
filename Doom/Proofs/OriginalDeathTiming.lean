import Doom.Proofs.OriginalRandomReturn
import Doom.Proofs.E1M1DeathSetter
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathTiming
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (nextIndex randomMemory randomByte random_value)

def code : List UInt8 := [0xe8,0x6a,0x9d,0xff,0xff,0x83,0xe0,0x03,0x8b,0x6b,0x60,0x29,0xc5,0x89,0x6b,0x60,0x83,0xfd,0x01,0x7d,0x07,0xc7,0x43,0x60,0x01,0,0,0]
def bytesProgram (timing rng : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a3f1 ≤ pc ∧ pc < 0x2a40d then X86Routine.decodeAt timing (pc-0x2a3f1)
  else if 0x24160 ≤ pc ∧ pc < 0x2417c then X86Routine.decodeAt rng (pc-0x24160)
  else none
def program := bytesProgram code Doom19.playRandomBytes

def tailListed : X86Routine.Program
  | 0x2a3f6 => some (.andRegister 0 3,3)
  | 0x2a3f9 => some (.control (.block (.legacy (.load 5 3 96))),3)
  | 0x2a3fc => some (.control (.block (.arithmetic (.sub 5 0))),2)
  | 0x2a3fe => some (.control (.block (.store ⟨some 3,none,0,96⟩ 5)),3)
  | 0x2a401 => some (.compareRegister 5 1,3)
  | 0x2a404 => some (.jumpSigned 0 7,2)
  | 0x2a406 => some (.storeImmediate ⟨some 3,none,0,96⟩ 1,7)
  | _ => none

def listed : X86Routine.Program := fun pc =>
  if pc=0x2a3f1 then some (.call (-25238),5)
  else if 0x24160 ≤ pc ∧ pc < 0x2417c then RandomReturn.rngListed pc else tailListed pc

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  unfold listed at h ⊢
  split
  · next hp => subst pc; decide
  · split
    · fun_cases RandomReturn.rngListed pc <;> simp_all [RandomReturn.rngListed] <;> decide
    · fun_cases tailListed pc <;> simp_all [tailListed] <;> decide

def amount (s : X86Memory.State) := s.regs 0 &&& (3#32)
def delta (s : X86Memory.State) := load32 s.memory (s.regs 3+(96#32))-amount s
def clamped (s : X86Memory.State) := if 1 ≤ (delta s).toInt then delta s else (1#32)
def tailEnd (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (amount s)) 5 (delta s),
    if 1 ≤ (delta s).toInt then store32 s.memory (s.regs 3+96) (delta s)
    else store32 (store32 s.memory (s.regs 3+96) (delta s)) (s.regs 3+96) 1⟩,
    some (compare32 (delta s) 1),0x2a40d⟩

/-- Both signed clamp branches, including wrapping subtraction, are executed. -/
theorem tail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run tailListed [0x2a40d] 7 ⟨s,f,0x2a3f6⟩=some (tailEnd s) := by
  have shadow (rs : Registers) (r : Reg) (a b : Word) : write (write rs r a) r b=write rs r b := by
    funext k; by_cases h : k=r <;> simp [write,h]
  by_cases ge : 1 ≤ (delta s).toInt
  all_goals
    have condition := ge
    simp [delta,amount] at condition
    try (replace condition := Int.not_le.mpr condition)
    simp [X86Routine.run,tailListed,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86.execute,X86Block.Address.eval,put,blockPreservesFlags,
      tailEnd,delta,amount,PlayerHeight.cmp_ge_prop,condition,write,shadow]
    try (funext r; by_cases h0 : r=0 <;> by_cases h5 : r=5 <;> simp_all [write])

def called (s : X86Memory.State) : X86Memory.State :=
  ⟨write s.regs 4 (s.regs 4-4),store32 s.memory (s.regs 4-4) 0x2a3f6⟩
def rolled (s : X86Memory.State) (i : UInt8) :=
  (RandomReturn.randomEnd ⟨0x2a3f6,by decide⟩ (called s) i (randomByte i)).core
def result (s : X86Memory.State) (i : UInt8) := tailEnd (rolled s i)
def writes (s : X86Memory.State) : List Word := [s.regs 4-4,0x12720,s.regs 3+96]
structure Inputs (s : X86Memory.State) (i : UInt8) : Prop where
  index : load32 s.memory (0x12720#32)=BitVec.ofNat 32 i.toNat
  table : s.memory ((0x1261c#32)+nextIndex i)=randomByte i
  indexSafe : Apart (0x12720#32) (s.regs 4-4)
  tableSafe : Apart ((0x1261c#32)+nextIndex i) (s.regs 4-4) ∧ Apart ((0x1261c#32)+nextIndex i) (0x12720#32)
  ticsSafe : Apart (s.regs 3+96) (s.regs 4-4) ∧ Apart (s.regs 3+96) (0x12720#32)

theorem rolled_regs (s : X86Memory.State) (i : UInt8) :
    (rolled s i).regs=write s.regs 0 ((randomByte i).zeroExtend 32) := by
  funext r
  by_cases h0 : r=0 <;> by_cases h4 : r=4 <;>
    simp [rolled,RandomReturn.randomEnd,called,write,h0,h4,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem random_frame (s : X86Memory.State) (i : UInt8) :
    PlayerHeight.Frame s.memory (rolled s i).memory [s.regs 4-4,0x12720] := by
  intro a safe
  simp only [rolled,RandomReturn.randomEnd,randomMemory,called]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]

theorem execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (h : Inputs s i) :
    X86Routine.run listed [0x2a40d] 15 ⟨s,f,0x2a3f1⟩=some (result s i) := by
  have index : load32 (called s).memory (0x12720#32)=BitVec.ofNat 32 i.toNat := by
    rw [called,load_store_apart _ _ _ _ h.indexSafe,h.index]
  have table : randomMemory (called s) i ((0x1261c#32)+nextIndex i)=randomByte i := by
    have eq := (random_frame s i).byte ((0x1261c#32)+nextIndex i) (by
      intro b hb; simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl; exact h.tableSafe.1; exact h.tableSafe.2)
    exact eq.trans h.table
  have ret : load32 (randomMemory (called s) i) ((called s).regs 4)=(0x2a3f6#32) := by
    have safe : Apart (s.regs 4-(4#32)) (0x12720#32) := by
      intro a b eq; exact h.indexSafe b a eq.symm
    simp [randomMemory,called,write,load_store_apart _ _ _ _ safe,load_store]
  have call : X86Routine.Prefix listed [0x2a40d] 1 ⟨s,f,0x2a3f1⟩ ⟨called s,f,0x24160⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨called s,f,0x24160⟩)
      (by change ¬((0x2a3f1:Nat) ∈ [0x2a40d]); decide)
      (show listed 0x2a3f1=some (.call (-25238),5) from by decide) (by
      simp [X86Routine.execute,X86Routine.pushWord,called,put,write])
    exact X86Routine.Prefix.nil _
  obtain ⟨n,hn,rpath,_⟩ := X86Routine.run_path
    (RandomReturn.random_execution ⟨0x2a3f6,by decide⟩ (by decide) (called s) f i (randomByte i) index table ret)
  have rpath := rpath.transfer listed [0x2a40d]
    (by intro pc hp; fun_cases RandomReturn.rngListed pc <;> simp_all [RandomReturn.rngListed,listed])
    (by intro pc hp; fun_cases RandomReturn.rngListed pc <;> simp_all [RandomReturn.rngListed])
  obtain ⟨k,hk,path,done⟩ := X86Routine.run_path (tail_execution (rolled s i) (some (logical32 ((randomByte i).zeroExtend 32))))
  have path := path.transfer listed [0x2a40d]
    (by intro pc hp; fun_cases tailListed pc <;> simp_all [tailListed,listed])
    (by intro pc hp; fun_cases tailListed pc <;> simp_all [tailListed])
  have tail : X86Routine.run listed [0x2a40d] 7 (RandomReturn.randomEnd ⟨0x2a3f6,by decide⟩ (called s) i (randomByte i))=some (result s i) :=
    path.finish (fuel := 0) (by simp [X86Routine.run,result,tailEnd]) 7 (by omega)
  exact call.finish (rpath.finish tail 14 (by omega)) 15 (by omega)

theorem original_execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (h : Inputs s i) :
    X86Routine.run program [0x2a40d] 15 ⟨s,f,0x2a3f1⟩=some (result s i) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f i h]; simp)]
  exact execution s f i h

theorem memory_frame (s : X86Memory.State) (i : UInt8) :
    PlayerHeight.Frame s.memory (result s i).core.memory (writes s) := by
  intro a safe
  unfold result tailEnd
  simp only [rolled_regs,write,show (3 : Reg) ≠ 0 by decide,↓reduceIte]
  split
  · rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
    exact random_frame s i a (fun b hb => safe b (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl|rfl <;> simp [writes]))
  · repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]
    exact random_frame s i a (fun b hb => safe b (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl|rfl <;> simp [writes]))

theorem result_tics (s : X86Memory.State) (i : UInt8) :
    load32 (result s i).core.memory (s.regs 3+96)=clamped (rolled s i) := by
  unfold result tailEnd clamped
  simp only [rolled_regs,write,show (3 : Reg) ≠ 0 by decide,↓reduceIte]
  split <;> simp [load_store]

theorem result_index (s : X86Memory.State) (i : UInt8) (h : Inputs s i) :
    load32 (result s i).core.memory (0x12720#32)=nextIndex i := by
  have safe : Apart (0x12720#32) (s.regs 3+(96#32)) := by
    intro a b eq; exact h.ticsSafe.2 b a eq.symm
  unfold result tailEnd
  simp only [rolled_regs,write,show (3 : Reg) ≠ 0 by decide,↓reduceIte]
  split <;> simp [load_store_apart _ _ _ _ safe,rolled,RandomReturn.randomEnd,randomMemory,load_store]

def playerTicks (extreme : Bool) (i : UInt8) : Word :=
  (E1M1DeathSetter.entry extreme).tics - ((randomByte i).zeroExtend 32 &&& (3#32))

/-- Exhaustive kernel reduction over precisely the two player entries and the
256 gameplay RNG indices, including 255 -> 0. This is not native_decide. -/
theorem player_table_facts : ∀ (extreme : Bool) (i : Fin 256),
    1 ≤ (playerTicks extreme (UInt8.ofNat i.val)).toInt ∧
    (playerTicks extreme (UInt8.ofNat i.val)) =
      (max (1 : Int32) (Int32.ofBitVec (E1M1DeathSetter.entry extreme).tics -
        Int32.ofNat (randomAt (UInt8.ofNat i.val+1) &&& 3))).toBitVec := by decide

theorem player_delta (s : X86Memory.State) (i : UInt8) (h : Inputs s i) (extreme : Bool)
    (tics : load32 s.memory (s.regs 3+96)=(E1M1DeathSetter.entry extreme).tics) :
    delta (rolled s i)=playerTicks extreme i := by
  have keep : load32 (rolled s i).memory (s.regs 3+(96#32))=load32 s.memory (s.regs 3+(96#32)) :=
    random_frame s i _ (by
      intro b hb
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl
      · exact h.ticsSafe.1
      · exact h.ticsSafe.2)
  simp only [delta,amount,rolled_regs,write,show (3 : Reg) ≠ 0 by decide,↓reduceIte,keep,playerTicks]
  have tickWord : load32 s.memory (s.regs 3+(96#32))=(E1M1DeathSetter.entry extreme).tics := by simpa using tics
  rw [tickWord]

theorem player_tics (s : X86Memory.State) (i : UInt8) (h : Inputs s i) (extreme : Bool)
    (tics : load32 s.memory (s.regs 3+96)=(E1M1DeathSetter.entry extreme).tics) :
    load32 (result s i).core.memory (s.regs 3+96)=playerTicks extreme i := by
  have facts := player_table_facts extreme ⟨i.toNat,i.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at facts
  rw [result_tics,clamped,player_delta s i h extreme tics,if_pos facts.1]

/-- The pure helper is called by the production death routine, after setState. -/
theorem live_timing (body : Death.Body) (world : Death.World) (extreme : Bool)
    (tics : body.tics=Int32.ofBitVec (E1M1DeathSetter.entry extreme).tics) :
    (Death.randomizeTics body world).1.tics.toBitVec=playerTicks extreme world.rng.play ∧
    (Death.randomizeTics body world).2.rng.play=world.rng.play+1 ∧
    (Death.randomizeTics body world).2.rng.misc=world.rng.misc ∧
    (Death.randomizeTics body world).2.events=world.events := by
  have facts := player_table_facts extreme ⟨world.rng.play.toNat,world.rng.play.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at facts
  exact ⟨by simpa [Death.randomizeTics,DoomRandom.nextPlay,tics] using facts.2.symm,rfl,rfl,rfl⟩

theorem live_correspondence (s : X86Memory.State) (f : Option Flags)
    (body : Death.Body) (world : Death.World) (extreme : Bool)
    (h : Inputs s world.rng.play)
    (memoryTics : load32 s.memory (s.regs 3+96)=(E1M1DeathSetter.entry extreme).tics)
    (bodyTics : body.tics=Int32.ofBitVec (E1M1DeathSetter.entry extreme).tics) :
    (X86Routine.run program [0x2a40d] 15 ⟨s,f,0x2a3f1⟩).map
      (fun t => (load32 t.core.memory (s.regs 3+96),load32 t.core.memory (0x12720#32))) =
    some ((Death.randomizeTics body world).1.tics.toBitVec,
      BitVec.ofNat 32 (Death.randomizeTics body world).2.rng.play.toNat) := by
  rw [original_execution s f world.rng.play h]
  simp only [Option.map_some]
  apply congrArg some
  apply Prod.ext
  · exact (player_tics s world.rng.play h extreme memoryTics).trans (live_timing body world extreme bodyTics).1.symm
  · exact result_index s world.rng.play h

end Doom.Proofs.DeathTiming
