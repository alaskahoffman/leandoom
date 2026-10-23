import Doom.Proofs.OriginalSectorSecret
import Doom.Verification.X86CodeMemory

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
namespace Doom.Proofs.SectorEntry
open Verification X86 X86Memory X86Control BlockSummary

def entryBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x89,0xc6,0x8b,0x00,0x8b,0x48,0x34,0x8b,0x09,0x8b,0x50,0x14,0x3b,0x11,0x0f,0x85,0x01,0x01,0x00,0x00,0x66,0x8b,0x51,0x0e,0x83,0xea,0x04,0x66,0x83,0xfa,0x0c,0x0f,0x87,0xde,0x00,0x00,0x00,0x81,0xe2,0xff,0xff,0x00,0x00,0x2e,0xff,0x24,0x95,0xec,0xfa,0x02,0x00]
def tableBytes : List UInt8 := [0xaa,0xfb,0x02,0x00,0x57,0xfb,0x02,0x00,0x27,0xfc,0x02,0x00,0x80,0xfb,0x02,0x00,0x27,0xfc,0x02,0x00,0xdc,0xfb,0x02,0x00,0x27,0xfc,0x02,0x00,0xed,0xfb,0x02,0x00,0x27,0xfc,0x02,0x00,0x27,0xfc,0x02,0x00,0x27,0xfc,0x02,0x00,0x27,0xfc,0x02,0x00,0xaa,0xfb,0x02,0x00]
def returnBytes : List UInt8 := [0x5e,0x5a,0x59,0x5b,0xc3]

/-- Code-object addresses are used directly as PCs and jump-table words. -/
def bytesProgram (entry secret epilogue : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2fb20 ≤ pc ∧ pc < 0x2fb20+entry.length then X86Routine.decodeAt entry (pc-0x2fb20)
  else if 0x2fbdc ≤ pc ∧ pc < 0x2fbdc+secret.length then X86Routine.decodeAt secret (pc-0x2fbdc)
  else if 0x2fc39 ≤ pc ∧ pc < 0x2fc39+epilogue.length then X86Routine.decodeAt epilogue (pc-0x2fc39)
  else none

def program := bytesProgram entryBytes SectorSecret.code returnBytes

def codeMemory (bytes : List UInt8) : Memory := fun a =>
  if 0x2faec ≤ a.toNat then ((bytes[a.toNat-0x2faec]?).getD 0).toBitVec else 0

def player (s : X86Memory.State) := s.regs 0
def object (s : X86Memory.State) := load32 s.memory (player s)
def subsector (s : X86Memory.State) := load32 s.memory (object s+(52#32))
def sector (s : X86Memory.State) := load32 s.memory (subsector s)
def zWord (s : X86Memory.State) := load32 s.memory (object s+(20#32))
def floorWord (s : X86Memory.State) := load32 s.memory (sector s)
def special (s : X86Memory.State) := load16 s.memory (sector s+(14#32))

def prepared (s : X86Memory.State) : X86Memory.State :=
  put (put (put (put (put s 6 (player s)) 0 (object s)) 1 (subsector s)) 1 (sector s)) 2 (zWord s)
def afterSwitch (s : X86Memory.State) : X86Memory.State := put (prepared s) 2 5

def listed : X86Routine.Program
  | 0x2fb24 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2fb26 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2fb28 => some (.control (.block (.legacy (.load 1 0 52))),3)
  | 0x2fb2b => some (.control (.block (.legacy (.load 1 1 0))),2)
  | 0x2fb2d => some (.control (.block (.legacy (.load 2 0 20))),3)
  | 0x2fb30 => some (.control (.cmpMemory 2 ⟨some 1,none,0,0⟩),2)
  | 0x2fb32 => some (.control (.jumpZero false 257),6)
  | 0x2fb38 => some (.loadHalf 2 ⟨some 1,none,0,14⟩,4)
  | 0x2fb3c => some (.addImmediate 2 (-4),3)
  | 0x2fb3f => some (.compareHalfRegister 2 12,4)
  | 0x2fb43 => some (.jumpAbove 222,6)
  | 0x2fb49 => some (.andRegister 2 65535,6)
  | 0x2fb4f => some (.jumpCode ⟨none,some 2,2,0x2faec⟩,8)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> rfl

theorem secret_table : load32 (codeMemory tableBytes) (0x2fb00#32) = (0x2fbdc#32) := by decide

theorem loaded_index (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (9#32)) + (-4#32)).extractLsb' 0 16 = 5 ∧
    (((z &&& (0xffff0000#32)) ||| (9#32)) + (-4#32)) &&& (65535#32) = 5 := by
  have low : ((((z &&& (0xffff0000#32)) ||| (9#32)) + (-4#32))).setWidth 16 = (5#16) := by
    rw [BitVec.setWidth_add _ _ (by decide)]
    simp only [BitVec.setWidth_or,BitVec.setWidth_and]
    change ((z.setWidth 16 &&& (0#16)) ||| (9#16)) + (65532#16) = (5#16)
    simp
  constructor
  · rw [← BitVec.setWidth_eq_extractLsb' (by decide : 16 ≤ 32)]
    exact low
  · change _ &&& (BitVec.allOnes 16).setWidth (16+16) = _
    rw [BitVec.and_setWidth_allOnes 16 16,low]
    rfl

theorem loaded_low (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (9#32)) + (4294967292#32)).extractLsb' 0 16 = (5#16) :=
  (loaded_index z).1
theorem loaded_mask (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (9#32)) + (4294967292#32)) &&& (65535#32) = (5#32) :=
  (loaded_index z).2

theorem sub_zero (a b : Word) : a-b = (0#32) ↔ a=b := by
  dsimp only [Word] at *
  bv_decide

/-- Start after the four PUSHes. The floor test and compiler switch are
executed, not supplied as intermediate assumptions. Their memory is unchanged. -/
theorem floor_prefix (s : X86Memory.State) (flags : Option Flags) :
    X86CodeMemory.Prefix (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 6 ⟨s,flags,0x2fb24⟩
      ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩ := by
  let s1 := put s 6 (player s)
  let s2 := put s1 0 (object s)
  let s3 := put s2 1 (subsector s)
  let s4 := put s3 1 (sector s)
  let s5 := put s4 2 (zWord s)
  apply X86CodeMemory.Prefix.step (middle := ⟨s1,flags,0x2fb26⟩)
    (by simp) (show listed 0x2fb24 = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨s2,flags,0x2fb28⟩)
    (by simp) (show listed 0x2fb26 = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨s3,flags,0x2fb2b⟩)
    (by simp) (show listed 0x2fb28 = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨s4,flags,0x2fb2d⟩)
    (by simp) (show listed 0x2fb2b = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨s5,flags,0x2fb30⟩)
    (by simp) (show listed 0x2fb2d = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  apply X86CodeMemory.Prefix.step (middle := ⟨s5,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩)
    (by simp) (show listed 0x2fb30 = _ from rfl) (by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,X86Block.execute,
        X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,s1,s2,s3,s4,s5,
        player,object,subsector,sector,zWord,floorWord,put,write])
  exact X86CodeMemory.Prefix.nil _

theorem switch_run (s : X86Memory.State) (flags : Option Flags)
    (isSecret : load16 s.memory (s.regs 1+(14#32)) = (9#16)) :
    X86CodeMemory.run (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 5 ⟨s,flags,0x2fb38⟩ =
      some ⟨put s 2 5,some {(logical32 5) with carry := some false},0x2fb4f⟩ := by
  let v := (s.regs 2 &&& (0xffff0000#32)) ||| (9#32)
  let s1 := put s 2 v
  let s2 := put s 2 (v + (4294967292#32))
  let f : Flags := {(X86Routine.compare16 (5#16) (12#16)) with carry := some true}
  have overwrite (t : X86Memory.State) (r : Reg) (a b : Word) : put (put t r a) r b = put t r b := by
    simp only [put]; congr 1; funext q; simp [write]; split <;> simp_all
  have path : X86CodeMemory.Prefix (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 5
      ⟨s,flags,0x2fb38⟩ ⟨put s 2 5,some {(logical32 5) with carry := some false},0x2fb4f⟩ := by
    apply X86CodeMemory.Prefix.step (middle := ⟨s1,flags,0x2fb3c⟩)
      (by simp) (show listed 0x2fb38 = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,X86Block.Address.eval,isSecret,s1,v])
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,none,0x2fb3f⟩)
      (by simp) (show listed 0x2fb3c = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,s1,s2,show (put s 2 v).regs 2 = v from by simp [put,write],overwrite])
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,some f,0x2fb43⟩)
      (by simp) (show listed 0x2fb3f = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,s2,put,write,v,loaded_low,f])
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,some f,0x2fb49⟩)
      (by simp) (show listed 0x2fb43 = _ from rfl) (by rfl)
    apply X86CodeMemory.Prefix.step (middle := ⟨put s 2 5,some {(logical32 5) with carry := some false},0x2fb4f⟩)
      (by simp) (show listed 0x2fb49 = _ from rfl) (by
        have mask : s2.regs 2 &&& (65535#32) = (5#32) := by simp [s2,put,write,v,loaded_mask]
        simp only [X86CodeMemory.execute,X86Routine.execute,mask]
        simp [s2,put,write,v,loaded_mask]
        funext r
        by_cases h : r = 2 <;> simp [write,h])
    exact X86CodeMemory.Prefix.nil _
  rw [show 5 = 5+0 from rfl,path.run 0]
  simp [X86CodeMemory.run]

theorem select_prefix (s : X86Memory.State) (flags : Option Flags) (isSecret : special s = 9) :
    X86CodeMemory.run (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 12 ⟨s,flags,0x2fb24⟩ =
      some (if zWord s = floorWord s then
        ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fb4f⟩
      else ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩) := by
  rw [(floor_prefix s flags).run 6]
  have d : listed 0x2fb32 = some (.control (.jumpZero false 257),6) := rfl
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground]
    have jump : X86CodeMemory.execute (codeMemory tableBytes) (.control (.jumpZero false 257))
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ := by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,compare32,ground]
    have tail := switch_run (prepared s) (some (compare32 (zWord s) (floorWord s)))
      (by simpa [prepared,put,write,special] using isSecret)
    have step : X86CodeMemory.Prefix (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 1
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ :=
      .step (by simp) d jump (.nil _)
    rw [show 6 = 1+5 from rfl,step.run 5]
    exact tail

  · rw [if_neg ground]
    have jump : X86CodeMemory.execute (codeMemory tableBytes) (.control (.jumpZero false 257))
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ := by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,compare32,sub_zero,ground]
    have step : X86CodeMemory.Prefix (codeMemory tableBytes) listed [0x2fb4f,0x2fc39] 1
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ :=
      .step (by simp) d jump (.nil _)
    rw [show 6 = 1+5 from rfl,step.run 5]
    simp [X86CodeMemory.run]

theorem select (s : X86Memory.State) (flags : Option Flags) (isSecret : special s = 9) :
    X86CodeMemory.run (codeMemory tableBytes) program [0x2fbdc,0x2fc39] 13 ⟨s,flags,0x2fb24⟩ =
      some (if zWord s = floorWord s then
        ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fbdc⟩
      else ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩) := by
  have pre := select_prefix s flags isSecret
  obtain ⟨k,bound,path,_⟩ := X86CodeMemory.run_path pre
  -- The prefix visits only the entry listing, never either final exit.
  have first := path.transfer program [0x2fbdc,0x2fc39] decoded (by
    intro pc hd
    fun_cases listed pc <;> simp_all [listed])
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground] at first
    have d : program 0x2fb4f = some (.jumpCode ⟨none,some 2,2,0x2faec⟩,8) := by decide
    have jump : X86CodeMemory.execute (codeMemory tableBytes) (.jumpCode ⟨none,some 2,2,0x2faec⟩)
        ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fb57⟩ =
        some ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fbdc⟩ := by
      simp only [X86CodeMemory.execute,X86Block.Address.eval,afterSwitch,put,write]
      simp [write,secret_table]
    have tail : X86CodeMemory.run (codeMemory tableBytes) program [0x2fbdc,0x2fc39] 1
        ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fb4f⟩ =
        some ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fbdc⟩ := by
      have step : X86CodeMemory.Prefix (codeMemory tableBytes) program [0x2fbdc,0x2fc39] 1
          ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fb4f⟩
          ⟨afterSwitch s,some {(logical32 5) with carry := some false},0x2fbdc⟩ :=
        .step (by simp) d jump (.nil _)
      rw [show 1 = 1+0 from rfl,step.run 0]
      simp [X86CodeMemory.run]

    simpa [ground] using first.finish tail 13 (by omega)
  · rw [if_neg ground] at first
    have tail : X86CodeMemory.run (codeMemory tableBytes) program [0x2fbdc,0x2fc39] 0
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ := by simp [X86CodeMemory.run]
    simpa [ground] using first.finish tail 13 (by omega)

/-- Both actual POP/RET sites have the same saved-word behavior. -/
theorem return_tail (s : X86Memory.State) (flags : Option Flags) (pc : Nat)
    (site : pc = 0x2fbe8 ∨ pc = 0x2fc39) (outside : 0x2fc3e ≤ SectorSecret.returnPc s) :
    X86CodeMemory.run (codeMemory tableBytes) program [SectorSecret.returnPc s] 5 ⟨s,flags,pc⟩ =
      some ⟨SectorSecret.restored s,flags,SectorSecret.returnPc s⟩ := by
  have d0 : program pc = some (.pop 6,1) := by rcases site with rfl|rfl <;> decide
  have d1 : program (pc+1) = some (.pop 2,1) := by rcases site with rfl|rfl <;> decide
  have d2 : program (pc+2) = some (.pop 1,1) := by rcases site with rfl|rfl <;> decide
  have d3 : program (pc+3) = some (.pop 3,1) := by rcases site with rfl|rfl <;> decide
  have d4 : program (pc+4) = some (.ret,1) := by rcases site with rfl|rfl <;> decide
  generalize hr : SectorSecret.returnPc s = ret at outside ⊢
  have hret : (load32 s.memory (s.regs 4+(16#32))).toNat = ret := hr
  have a0 : pc ≠ ret := by omega
  have a1 : pc+1 ≠ ret := by omega
  have a2 : pc+2 ≠ ret := by omega
  have a3 : pc+3 ≠ ret := by omega
  have a4 : pc+4 ≠ ret := by omega
  simp [X86CodeMemory.run,d0,d1,d2,d3,d4,a0,a1,a2,a3,a4,Nat.add_assoc,
    X86CodeMemory.execute,X86Routine.execute,SectorSecret.restored,put,write,BitVec.add_assoc,hret]
  funext r
  by_cases h4 : r = 4 <;> simp [write,h4]

theorem secret_tail (s : X86Memory.State) (flags : Option Flags)
    (safe : SectorSecret.StackSafe s) (outside : 0x2fc3e ≤ SectorSecret.returnPc s) :
    X86CodeMemory.run (codeMemory tableBytes) program [SectorSecret.returnPc s] 7 ⟨s,flags,0x2fbdc⟩ =
      some ⟨SectorSecret.final s,none,SectorSecret.returnPc s⟩ := by
  have d0 : program 0x2fbdc = some (.incrementMemory ⟨some 6,none,0,212⟩,6) := by decide
  have d6 : program 0x2fbe2 = some (.storeHalfImmediate ⟨some 1,none,0,14⟩ 0,6) := by decide
  have first : X86CodeMemory.Prefix (codeMemory tableBytes) program [SectorSecret.returnPc s] 2
      ⟨s,flags,0x2fbdc⟩ ⟨SectorSecret.updated s,none,0x2fbe8⟩ := by
    apply X86CodeMemory.Prefix.step (by simp only [List.mem_singleton]; omega) d0 (by rfl)
    apply X86CodeMemory.Prefix.step (by simp only [List.mem_singleton]; omega) d6 (by rfl)
    simpa [SectorSecret.updated,SectorSecret.count,SectorSecret.countAddress,SectorSecret.specialAddress,X86Block.Address.eval] using
      (X86CodeMemory.Prefix.nil (cm := codeMemory tableBytes) (program := program) (exits := [SectorSecret.returnPc s])
        (⟨SectorSecret.updated s,none,0x2fbe8⟩ : X86Control.State))
  have tail := return_tail (SectorSecret.updated s) none 0x2fbe8 (Or.inl rfl)
    (by rw [SectorSecret.updated_return s safe]; exact outside)
  rw [SectorSecret.updated_return s safe,SectorSecret.updated_restored s safe] at tail
  exact first.finish tail 7 (by decide)

structure Inputs (s : X86Memory.State) (z floor : Fixed) (n : Int32) : Prop where
  isSecret : special s = 9
  height : zWord s = z.raw.toBitVec
  floor : floorWord s = floor.raw.toBitVec
  count : load32 s.memory (player s+(212#32)) = n.toBitVec
  separate : SectorSecret.Separate (afterSwitch s)
  stack : SectorSecret.StackSafe (afterSwitch s)
  outside : 0x2fc3e ≤ SectorSecret.returnPc s

def result (s : X86Memory.State) : X86Control.State :=
  if zWord s = floorWord s then ⟨SectorSecret.final (afterSwitch s),none,SectorSecret.returnPc s⟩
  else ⟨SectorSecret.restored (prepared s),some (compare32 (zWord s) (floorWord s)),SectorSecret.returnPc s⟩

theorem program_bound (pc : Nat) (valid : program pc ≠ none) : pc < 0x2fc3e := by
  unfold program bytesProgram at valid
  split at valid
  next h => change _ ∧ pc < 0x2fb20+55 at h; omega
  next h =>
    split at valid
    next h => change _ ∧ pc < 0x2fbdc+17 at h; omega
    next h =>
      split at valid
      next h => change _ ∧ pc < 0x2fc39+5 at h; omega
      next h => simp_all

/-- A continuous floor-check/switch/case/return execution, from immediately
after the four PUSHes. Only initial-state contracts are supplied. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs s z floor n) :
    X86CodeMemory.run (codeMemory tableBytes) program [SectorSecret.returnPc s] 20 ⟨s,flags,0x2fb24⟩ = some (result s) := by
  have selection := select s flags h.isSecret
  obtain ⟨k,bound,path,_⟩ := X86CodeMemory.run_path selection
  have first := path.transfer program [SectorSecret.returnPc s] (fun _ _ => rfl) (by
    intro pc hd; have hb := program_bound pc hd; have ho := h.outside; simp only [List.mem_singleton]; omega)
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground] at first
    have tail := secret_tail (afterSwitch s) (some {(logical32 5) with carry := some false}) h.stack
      (by simpa [SectorSecret.returnPc,afterSwitch,prepared,put,write] using h.outside)
    have ret : SectorSecret.returnPc (afterSwitch s) = SectorSecret.returnPc s := by
      simp [SectorSecret.returnPc,afterSwitch,prepared,put,write]
    rw [ret] at tail
    simpa [result,ground] using first.finish tail 20 (by omega)
  · rw [if_neg ground] at first
    have tail := return_tail (prepared s) (some (compare32 (zWord s) (floorWord s))) 0x2fc39 (Or.inr rfl)
      (by simpa [SectorSecret.returnPc,prepared,put,write] using h.outside)
    have ret : SectorSecret.returnPc (prepared s) = SectorSecret.returnPc s := by
      simp [SectorSecret.returnPc,prepared,put,write]
    rw [ret] at tail
    simpa [result,ground] using first.finish tail 20 (by omega)

/-- Both floor outcomes match the live secret helper. In particular, being
above OR below the sector floor skips discovery; collision floorz is irrelevant. -/
theorem fields (s : X86Memory.State) (z floor : Fixed) (n : Int32) (h : Inputs s z floor n) :
    (load16 (result s).core.memory (sector s+(14#32)),load32 (result s).core.memory (player s+(212#32))) =
      (BitVec.ofNat 16 (LevelSpecials.secret 9 z floor n).1,(LevelSpecials.secret 9 z floor n).2.toBitVec) := by
  have eq : zWord s = floorWord s ↔ z = floor := by
    rw [h.height,h.floor,Int32.toBitVec_inj]
    cases z; cases floor; simp
  by_cases ground : zWord s = floorWord s
  · have onFloor := eq.mp ground
    have live := SectorSecret.secret_fields (afterSwitch s) n z floor onFloor
      (by simpa [SectorSecret.specialAddress,afterSwitch,prepared,put,write,special] using h.isSecret)
      (by simpa [SectorSecret.count,SectorSecret.countAddress,afterSwitch,prepared,put,write] using h.count) h.separate
    simpa [result,ground,SectorSecret.specialAddress,SectorSecret.countAddress,afterSwitch,prepared,put,write,
      special,show load16 s.memory (sector s+(14#32)) = 9 from h.isSecret] using live
  · have ne : z ≠ floor := fun e => ground (eq.mpr e)
    have neRaw : z.raw ≠ floor.raw := by cases z; cases floor; simpa using ne
    have different : (z == floor) = false := by change (z.raw == floor.raw) = false; simp [neRaw]
    simp [result,ground,SectorSecret.restored,prepared,put,write,LevelSpecials.secret,different,
      show load16 s.memory (sector s+(14#32)) = 9 from h.isSecret,h.count]

theorem observation (s : X86Memory.State) (flags : Option Flags) (z floor : Fixed) (n : Int32)
    (h : Inputs s z floor n) :
    (X86CodeMemory.run (codeMemory tableBytes) program [SectorSecret.returnPc s] 20 ⟨s,flags,0x2fb24⟩).map
      (fun t => (t.pc,load16 t.core.memory (sector s+(14#32)),load32 t.core.memory (player s+(212#32)),t.core.regs 4)) =
      some (SectorSecret.returnPc s,BitVec.ofNat 16 (LevelSpecials.secret 9 z floor n).1,
        (LevelSpecials.secret 9 z floor n).2.toBitVec,s.regs 4+20) := by
  rw [execution s flags z floor n h]
  have f := fields s z floor n h
  simp only [Prod.mk.injEq] at f
  simp only [Option.map_some,f.1,f.2]
  by_cases ground : zWord s = floorWord s <;>
    simp [result,ground,SectorSecret.final,SectorSecret.restored,afterSwitch,prepared,put,write]

end Doom.Proofs.SectorEntry
