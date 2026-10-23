import Doom.Verification.X86Control

/-! A limited interprocedural extension of X86Control. PCs are offsets from a
chosen common code origin; data/stack addresses remain flat 32-bit words. Only listed encodings
are decoded. Unsupported callees and instruction forms fail closed. Indirect memory CALL targets use the same code origin as PCs. CS-relative jumps require the separate code-memory interpreter. Arithmetic
flags not needed by this path are invalidated. This is not a DOS loader or a
complete x86 semantics. -/
namespace Doom.Verification.X86Routine
open X86 X86Memory X86Block X86Control

inductive Op where
  | control (op : X86Control.Op)
  | andByteImmediate (dst : Reg) (mask : BitVec 8)
  | orByteImmediate (dst : Reg) (value : BitVec 8)
  | storeByte (address : Address) (src : Reg)
  | compareByte (address : Address) (value : BitVec 8)
  | compareHalf (address : Address) (value : BitVec 16)
  | storeHalf (address : Address) (src : Reg)
  | storeHalfImmediate (address : Address) (value : BitVec 16)
  | addHalfImmediate (address : Address) (value : BitVec 16)
  | incrementMemory (address : Address)
  | decrementMemory (address : Address)
  | loadHalf (dst : Reg) (address : Address)
  | loadSignedHalf (dst : Reg) (address : Address)
  | compareHalfRegister (src : Reg) (value : BitVec 16)
  | jumpAbove (offset : Int)
  | jumpUnsigned (condition : Nat) (offset : Int)
  | xorHalf (dst src : Reg)
  | andMemoryByte (address : Address) (mask : BitVec 8)
  | orRegister (dst : Reg) (mask : Word)
  | andRegister (dst : Reg) (mask : Word)
  | xorMemory (dst : Reg) (address : Address)
  | xorRegister (dst src : Reg)
  | jumpCode (address : Address)
  | immediate (dst : Reg) (value : Word)
  | multiplyImmediate (dst src : Reg) (value : Word)
  | multiplyRegister (dst src : Reg)
  | multiplyLoaded (dst : Reg) (address : Address)
  | addImmediate (dst : Reg) (value : Word)
  | addMemory (dst : Reg) (address : Address)
  | subMemory (dst : Reg) (address : Address)
  | subRegistersWithFlags (dst src : Reg)
  | push (src : Reg)
  | pushImmediate (value : Word)
  | pop (dst : Reg)
  | call (offset : Int)
  | callMemory (address : Address)
  | ret
  | jump (offset : Int)
  | compareRegister (lhs : Reg) (rhs : Word)
  | compareRegisters (lhs rhs : Reg)
  | storeImmediate (address : Address) (value : Word)
  | testMemoryByte (address : Address) (mask : BitVec 8)
  | multiplyMemory (dst : Reg) (address : Address) (value : Word)
  | sar (dst : Reg) (amount : UInt8)
  | negateRegister (dst : Reg)
  | signedDivide (src : Reg)
  | cdq
  | shld (dst src : Reg) (amount : UInt8)
  | setLess (dst : Reg)
  | setGreater (dst : Reg)
  | jumpSigned (condition : Nat) (offset : Int)
  | moveByte (dst src : Reg)
  | testRegisterImmediate (src : Reg) (mask : Word)
  | testByteImmediate (src : Reg) (mask : BitVec 8)
  | storeByteImmediate (address : Address) (value : BitVec 8)
  deriving DecidableEq

def decode (code : List UInt8) : Option (Op × List UInt8) :=
  match code with
  | 0x68 :: tail => do
      let (v,tail) ← word tail
      pure (.pushImmediate v,tail)
  | 0x6a :: v :: tail => some (.pushImmediate (v.toBitVec.signExtend 32),tail)
  | 0xa9 :: tail => do
      let (v,tail) ← word tail
      pure (.testRegisterImmediate 0 v,tail)
  | 0x99 :: tail => some (.cdq,tail)
  | 0x2e :: 0xff :: m :: tail => do
      if m.toNat / 8 % 8 != 4 then none else do
        let (a,tail) ← operand m tail
        pure (.jumpCode a,tail)
  | 0x66 :: 0x31 :: m :: tail =>
      if m.toNat / 64 = 3 then some (.xorHalf (rm m) (reg m),tail) else none
  | 0x3d :: tail => do
      let (v,tail) ← word tail
      pure (.compareRegister 0 v,tail)
  | 0x72 :: d :: tail => some (.jumpUnsigned 0 d.toBitVec.toInt,tail)
  | 0x73 :: d :: tail => some (.jumpUnsigned 2 d.toBitVec.toInt,tail)
  | 0x76 :: d :: tail => some (.jumpUnsigned 1 d.toBitVec.toInt,tail)
  | 0x66 :: 0x89 :: m :: tail => do
      let (a,tail) ← operand m tail
      pure (.storeHalf a (reg m),tail)
  | 0x66 :: 0x8b :: m :: tail => do
      let (a,tail) ← operand m tail
      pure (.loadHalf (reg m) a,tail)
  | 0x0f :: opcode :: tail =>
      if opcode = 0xaf then do
        let m :: tail := tail | none
        if m.toNat / 64 = 3 then pure (.multiplyRegister (reg m) (rm m),tail)
        else
          let (a,tail) ← operand m tail
          pure (.multiplyLoaded (reg m) a,tail)
      else if opcode = 0xbf then
        -- Keep existing simple MOVSX decodings stable; add full memory addressing.
        match X86Control.decode code with
        | some (op,rest) => some (.control op,rest)
        | none => do
          let m :: tail := tail | none
          let (a,tail) ← operand m tail
          pure (.loadSignedHalf (reg m) a,tail)
      else if opcode = 0x9c then do
        let m :: tail := tail | none
        if m.toNat / 64 = 3 then pure (.setLess (rm m),tail) else none
      else if opcode = 0x9f then do
        let m :: tail := tail | none
        if m.toNat / 64 = 3 then pure (.setGreater (rm m),tail) else none
      else if opcode = 0xa4 then do
        let m :: n :: tail := tail | none
        if m.toNat / 64 = 3 then pure (.shld (rm m) (reg m) n,tail) else none
      else if opcode = 0x84 || opcode = 0x85 then do
        let (v,tail) ← word tail
        pure (.control (.jumpZero (opcode = 0x84) v.toInt),tail)
      else if opcode = 0x8c then do
        let (v,tail) ← word tail
        pure (.jumpSigned 3 v.toInt,tail)
      else if opcode = 0x8e then do
        let (v,tail) ← word tail
        pure (.jumpSigned 1 v.toInt,tail)
      else if opcode = 0x8d then do
        let (v,tail) ← word tail
        pure (.jumpSigned 0 v.toInt,tail)
      else if opcode = 0x8f then do
        let (v,tail) ← word tail
        pure (.jumpSigned 2 v.toInt,tail)
      else if opcode = 0x82 then do
        let (v,tail) ← word tail
        pure (.jumpUnsigned 0 v.toInt,tail)
      else if opcode = 0x87 then do
        let (v,tail) ← word tail
        pure (.jumpAbove v.toInt,tail)
      else (X86Control.decode code).map (fun (i,rest) => (.control i,rest))
  | 0xff :: m :: tail => do
      let (a,tail) ← operand m tail
      if m.toNat / 8 % 8 = 0 then pure (.incrementMemory a,tail)
      else if m.toNat / 8 % 8 = 1 then pure (.decrementMemory a,tail)
      else if m.toNat / 8 % 8 = 2 then pure (.callMemory a,tail)
      else none
  | 0x66 :: 0xc7 :: m :: tail => do
      if m.toNat / 8 % 8 != 0 then none else do
        let (a,tail) ← operand m tail
        let lo :: hi :: tail := tail | none
        pure (.storeHalfImmediate a (hi.toBitVec ++ lo.toBitVec),tail)
  | 0x66 :: 0x83 :: m :: tail => do
      if m.toNat / 8 % 8 = 0 && m.toNat / 64 != 3 then do
        let (a,tail) ← operand m tail
        let v :: tail := tail | none
        pure (.addHalfImmediate a (v.toBitVec.signExtend 16),tail)
      else if m.toNat / 8 % 8 != 7 then none
      else if m.toNat / 64 = 3 then do
        let v :: tail := tail | none
        pure (.compareHalfRegister (rm m) (v.toBitVec.signExtend 16),tail)
      else do
        let (a,tail) ← operand m tail
        let v :: tail := tail | none
        pure (.compareHalf a (v.toBitVec.signExtend 16),tail)
  | 0x80 :: m :: tail => do
    if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 1 then do
      let v :: tail := tail | none
      pure (.orByteImmediate (rm m) v.toBitVec,tail)
    else if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 4 then do
      let v :: tail := tail | none
      pure (.andByteImmediate (rm m) v.toBitVec,tail)
    else if m.toNat / 64 != 3 && m.toNat / 8 % 8 = 4 then do
      let (a,tail) ← operand m tail
      let v :: tail := tail | none
      pure (.andMemoryByte a v.toBitVec,tail)
    else if m.toNat / 8 % 8 != 7 then none else do
      let (a,tail) ← operand m tail
      let v :: tail := tail | none
      pure (.compareByte a v.toBitVec,tail)
  | 0x88 :: m :: tail => do
      if m.toNat / 64 = 3 then pure (.moveByte (rm m) (reg m),tail)
      else do
        let (a,tail) ← operand m tail
        pure (.storeByte a (reg m),tail)
  | 0x24 :: v :: tail => some (.andByteImmediate 0 v.toBitVec,tail)
  | 0xc6 :: m :: tail => do
      if m.toNat / 8 % 8 != 0 then none else do
        let (a,tail) ← operand m tail
        let v :: tail := tail | none
        pure (.storeByteImmediate a v.toBitVec,tail)
  | 0x81 :: m :: tail =>
    if m.toNat / 8 % 8 = 7 && m.toNat / 64 = 3 then do
      let (v,tail) ← word tail
      pure (.compareRegister (rm m) v,tail)
    else if m.toNat / 8 % 8 = 7 then do
      let (a,tail) ← operand m tail
      let (v,tail) ← word tail
      pure (.control (.cmpImmediate a v),tail)
    else if m.toNat / 8 % 8 = 1 && m.toNat / 64 = 3 then do
      let (v,tail) ← word tail
      pure (.orRegister (rm m) v,tail)
    else if m.toNat / 8 % 8 = 4 && m.toNat / 64 = 3 then do
      let (v,tail) ← word tail
      pure (.andRegister (rm m) v,tail)
    else if m.toNat / 8 % 8 = 5 && m.toNat / 64 = 3 then do
      let (v,tail) ← word tail
      pure (.addImmediate (rm m) (-v),tail)
    else if m.toNat / 8 % 8 = 0 && m.toNat / 64 = 3 then do
      let (v,tail) ← word tail
      pure (.addImmediate (rm m) v,tail)
    else none
  | 0x83 :: m :: v :: tail =>
    if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 0 then
      some (.addImmediate (rm m) (v.toBitVec.signExtend 32),tail)
    else if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 5 then
      some (.addImmediate (rm m) (-(v.toBitVec.signExtend 32)),tail)
    else if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 4 then
      some (.andRegister (rm m) (v.toBitVec.signExtend 32),tail)
    else if m.toNat / 64 = 3 && m.toNat / 8 % 8 = 7 then
      some (.compareRegister (rm m) (v.toBitVec.signExtend 32),tail)
    else (X86Control.decode code).map (fun (i,rest) => (.control i,rest))
  | 0x6b :: m :: v :: tail =>
    if m.toNat / 64 = 3 then some (.multiplyImmediate (reg m) (rm m) (v.toBitVec.signExtend 32),tail) else none
  | 0xe8 :: tail => do
    let (v,tail) ← word tail
    pure (.call v.toInt,tail)
  | 0xeb :: d :: tail => some (.jump d.toBitVec.toInt,tail)
  | 0xe9 :: tail => do
      let (v,tail) ← word tail
      pure (.jump v.toInt,tail)
  | 0x7c :: d :: tail => some (.jumpSigned 3 d.toBitVec.toInt,tail)
  | 0x7d :: d :: tail => some (.jumpSigned 0 d.toBitVec.toInt,tail)
  | 0x7e :: d :: tail => some (.jumpSigned 1 d.toBitVec.toInt,tail)
  | 0x7f :: d :: tail => some (.jumpSigned 2 d.toBitVec.toInt,tail)
  | 0x39 :: m :: tail =>
      if m.toNat / 64 = 3 then some (.compareRegisters (rm m) (reg m),tail) else none
  | 0xc7 :: m :: tail => do
      if m.toNat / 8 % 8 != 0 then none else do
        let (a,tail) ← operand m tail
        let (v,tail) ← word tail
        pure (.storeImmediate a v,tail)
  | 0xf7 :: m :: tail =>
      if m.toNat / 8 = 24 then do
        let (v,tail) ← word tail
        pure (.testRegisterImmediate (rm m) v,tail)
      else if m.toNat / 8 = 27 then some (.negateRegister (rm m),tail)
      else if m.toNat / 8 = 31 then some (.signedDivide (rm m),tail)
      else (X86Control.decode code).map (fun (i,rest) => (.control i,rest))
  | 0xf6 :: m :: tail => do
      if m.toNat / 8 % 8 != 0 then none else do
        if m.toNat / 64 = 3 then do
          let v :: tail := tail | none
          pure (.testByteImmediate (rm m) v.toBitVec,tail)
        else do
          let (a,tail) ← operand m tail
          let v :: tail := tail | none
          pure (.testMemoryByte a v.toBitVec,tail)
  | 0x69 :: m :: tail => do
      let (a,tail) ← operand m tail
      let (v,tail) ← word tail
      pure (.multiplyMemory (reg m) a v,tail)
  | 0xc1 :: m :: n :: tail =>
      if m.toNat / 8 = 31 then some (.sar (rm m) n,tail)
      else (X86Control.decode code).map (fun (i,rest) => (.control i,rest))
  | 0xd1 :: m :: tail =>
      if m.toNat / 8 = 31 then some (.sar (rm m) 1,tail) else none
  | 0x33 :: m :: tail => do
      let (a,tail) ← operand m tail
      pure (.xorMemory (reg m) a,tail)
  | 0x31 :: m :: tail =>
      if m.toNat / 64 = 3 then some (.xorRegister (rm m) (reg m),tail) else none
  | 0x03 :: m :: tail => do
      let (a,tail) ← operand m tail
      pure (.addMemory (reg m) a,tail)
  | 0x2b :: m :: tail =>
      if m.toNat / 64 = 3 then some (.control (.block (.arithmetic (.sub (reg m) (rm m)))),tail)
      else do
        let (a,tail) ← operand m tail
        pure (.subMemory (reg m) a,tail)
  | 0x05 :: tail => do
      let (v,tail) ← word tail
      pure (.addImmediate 0 v,tail)
  | 0xa1 :: tail => do
      let (a,tail) ← word tail
      pure (.control (.block (.load 0 ⟨none,none,0,a⟩)),tail)
  -- INC's register result is addition; discard flags conservatively, as for
  -- ADD here. In particular this does not claim to reproduce INC's saved CF.
  | 0x40 :: tail => some (.addImmediate 0 1,tail)
  | 0x41 :: tail => some (.addImmediate 1 1,tail)
  | 0x42 :: tail => some (.addImmediate 2 1,tail)
  | 0x43 :: tail => some (.addImmediate 3 1,tail)
  | 0x45 :: tail => some (.addImmediate 5 1,tail)
  | 0x46 :: tail => some (.addImmediate 6 1,tail)
  | 0x47 :: tail => some (.addImmediate 7 1,tail)
  -- DEC ESI in P_TraverseIntercepts. The register result wraps; as with INC,
  -- flags are forgotten. The following TEST establishes all flags used here.
  | 0x4e :: tail => some (.addImmediate 6 (-1),tail)
  | 0xc3 :: tail => some (.ret,tail)
  | op :: tail =>
    if 0xb8 ≤ op.toNat && op.toNat ≤ 0xbf then do
      let (v,tail) ← word tail
      pure (.immediate (Fin.ofNat 8 (op.toNat-0xb8)) v,tail)
    else if 0x50 ≤ op.toNat && op.toNat ≤ 0x57 then
      some (.push (Fin.ofNat 8 (op.toNat-0x50)),tail)
    else if 0x58 ≤ op.toNat && op.toNat ≤ 0x5f then
      some (.pop (Fin.ofNat 8 (op.toNat-0x58)),tail)
    else (X86Control.decode code).map (fun (i,rest) => (.control i,rest))
  | [] => none

def compare8 (a b : BitVec 8) : Flags :=
  let result := a-b
  ⟨result == 0,result.msb,(a.msb != b.msb) && (result.msb != a.msb),none⟩

/-- Operand-size-16 CMP: subtraction and flags are computed at 16 bits. -/
def compare16 (a b : BitVec 16) : Flags :=
  let result := a-b
  ⟨result == 0,result.msb,(a.msb != b.msb) && (result.msb != a.msb),none⟩

/-- Little-endian two-byte store, with 32-bit wrapping addresses. -/
def store16 (m : Memory) (a : Word) (value : BitVec 16) : Memory := fun b =>
  if b = a then value.extractLsb' 0 8
  else if b = a+1 then value.extractLsb' 8 8 else m b

def pushWord (s : X86Memory.State) (value : Word) : X86Memory.State :=
  { regs := write s.regs 4 (s.regs 4 - (4#32))
    memory := store32 s.memory (s.regs 4 - (4#32)) value }

/-- PC is already advanced to the following instruction. CALL saves that
address before branching; RET reads it back through the same byte memory. -/
def execute (op : Op) (s : X86Control.State) : Option X86Control.State := match op with
  | .control op => X86Control.execute op s
  | .subRegistersWithFlags dst src =>
      some {s with
        core := put s.core dst (s.core.regs dst - s.core.regs src)
        flags := some (compare32 (s.core.regs dst) (s.core.regs src))}
  | .moveByte dst src => some {s with core := putByte s.core dst (readByte s.core.regs src)}
  | .testRegisterImmediate src mask =>
      some {s with flags := some (logical32 (s.core.regs src &&& mask))}
  | .testByteImmediate src mask =>
      some {s with flags := some (logical8 (readByte s.core.regs src &&& mask))}
  | .storeByteImmediate address value =>
      let a := address.eval s.core.regs
      some {s with core := {s.core with memory := fun b => if b=a then value else s.core.memory b}}
  | .andByteImmediate dst mask =>
      let value := readByte s.core.regs dst &&& mask
      some {s with core := putByte s.core dst value, flags := some {(logical8 value) with carry := some false}}
  | .orByteImmediate dst value =>
      let result := readByte s.core.regs dst ||| value
      some {s with core := putByte s.core dst result, flags := some (logical8 result)}
  | .storeByte address src =>
      let a := address.eval s.core.regs
      let value := readByte s.core.regs src
      some {s with core := {s.core with memory := fun b => if b = a then value else s.core.memory b}}
  | .compareByte a v => some {s with flags := some (compare8 (s.core.memory (a.eval s.core.regs)) v)}
  | .compareHalf a v => some {s with flags := some (compare16 (load16 s.core.memory (a.eval s.core.regs)) v)}
  | .storeHalf a r => some {s with core := {s.core with
      memory := store16 s.core.memory (a.eval s.core.regs) ((s.core.regs r).extractLsb' 0 16)}}
  | .storeHalfImmediate a v => some {s with core := {s.core with memory := store16 s.core.memory (a.eval s.core.regs) v}}
  | .addHalfImmediate a v => some {s with
      core := {s.core with memory := store16 s.core.memory (a.eval s.core.regs) (load16 s.core.memory (a.eval s.core.regs)+v)}
      flags := none}
  | .incrementMemory a => some {s with
      core := {s.core with memory := store32 s.core.memory (a.eval s.core.regs) (load32 s.core.memory (a.eval s.core.regs) + 1)}
      flags := none}
  -- DEC preserves CF on hardware; this projection conservatively forgets all
  -- flags. A later branch must establish fresh flags before using them.
  | .decrementMemory a => some {s with
      core := {s.core with memory := store32 s.core.memory (a.eval s.core.regs) (load32 s.core.memory (a.eval s.core.regs) - 1)}
      flags := none}
  | .loadSignedHalf r a => some {s with core := put s.core r ((load16 s.core.memory (a.eval s.core.regs)).signExtend 32)}
  | .loadHalf r a => some {s with core := put s.core r ((s.core.regs r &&& 0xffff0000) |||
      (load16 s.core.memory (a.eval s.core.regs)).zeroExtend 32)}
  | .compareHalfRegister r v =>
      let lhs := (s.core.regs r).extractLsb' 0 16
      some {s with flags := some {(compare16 lhs v) with carry := some (lhs.ult v)}}
  | .jumpAbove offset => do
      let flags ← s.flags
      let carry ← flags.carry
      if !carry && !flags.zero then
        let target := (s.pc : Int) + offset
        if target < 0 ∨ target ≥ 4294967296 then none else some {s with pc := target.toNat}
      else some s
  | .jumpUnsigned condition offset => do
      let flags ← s.flags
      let carry ← flags.carry
      let take ← match condition with
        | 0 => some carry
        | 1 => some (carry || flags.zero)
        | 2 => some (!carry)
        | _ => none
      if take then
        let target := (s.pc : Int) + offset
        if target < 0 ∨ target ≥ 4294967296 then none else some {s with pc := target.toNat}
      else some s
  | .xorHalf dst src =>
      let value := (s.core.regs dst ^^^ s.core.regs src).extractLsb' 0 16
      some {s with core := put s.core dst ((s.core.regs dst &&& 0xffff0000) ||| value.zeroExtend 32), flags := some ⟨value == 0,value.msb,false,some false⟩}
  | .xorMemory dst address =>
      let value := s.core.regs dst ^^^ load32 s.core.memory (address.eval s.core.regs)
      some {s with core := put s.core dst value,flags := some (logical32 value)}
  | .xorRegister dst src =>
      let value := s.core.regs dst ^^^ s.core.regs src
      some {s with core := put s.core dst value,flags := some {(logical32 value) with carry := some false}}
  | .andMemoryByte address mask =>
      let a := address.eval s.core.regs
      let value := s.core.memory a &&& mask
      some {s with
        core := {s.core with memory := fun b => if b=a then value else s.core.memory b}
        flags := some {(logical8 value) with carry := some false}}
  | .orRegister r mask =>
      let value := s.core.regs r ||| mask
      some {s with core := put s.core r value,flags := some {(logical32 value) with carry := some false}}
  | .andRegister r mask =>
      let value := s.core.regs r &&& mask
      some {s with core := put s.core r value,flags := some {(logical32 value) with carry := some false}}
  | .jumpCode _ => none -- requires an explicit code-segment memory interpretation
  | .immediate r v => some {s with core := put s.core r v}
  -- Two-operand IMUL keeps the low 32 bits. Overflow/carry are not consumed
  -- by these proofs; conservatively invalidate flags rather than inventing them.
  | .multiplyRegister dst src => some {s with core := put s.core dst (s.core.regs dst * s.core.regs src),flags := none}
  | .multiplyLoaded dst a => some {s with core := put s.core dst (s.core.regs dst * load32 s.core.memory (a.eval s.core.regs)),flags := none}
  | .multiplyImmediate dst src v => some {s with core := put s.core dst (s.core.regs src * v),flags := none}
  | .addImmediate dst v => some {s with core := put s.core dst (s.core.regs dst + v),flags := none}
  -- Read the complete operand from the pre-instruction state, including when
  -- its effective address uses dst. Arithmetic flags are conservatively unknown.
  | .addMemory dst a => some {s with core := put s.core dst (s.core.regs dst + load32 s.core.memory (a.eval s.core.regs)),flags := none}
  | .subMemory dst a => some {s with core := put s.core dst (s.core.regs dst - load32 s.core.memory (a.eval s.core.regs)),flags := none}
  | .pushImmediate v => some {s with core := pushWord s.core v}
  | .push src => some {s with core := pushWord s.core (s.core.regs src)}
  | .pop dst =>
    let value := load32 s.core.memory (s.core.regs 4)
    some {s with core := put (put s.core 4 (s.core.regs 4 + (4#32))) dst value}
  | .call offset =>
    let target := (s.pc : Int) + offset
    if target < 0 ∨ target ≥ 4294967296 ∨ s.pc ≥ 4294967296 then none else
      some {s with core := pushWord s.core (BitVec.ofNat 32 s.pc),pc := target.toNat}
  | .callMemory address =>
    -- Evaluate the target before pushing: the operand may itself use ESP.
    if s.pc ≥ 4294967296 then none else
      some {s with core := pushWord s.core (BitVec.ofNat 32 s.pc),pc := (load32 s.core.memory (address.eval s.core.regs)).toNat}
  | .jump offset =>
    let target := (s.pc : Int) + offset
    if target < 0 ∨ target ≥ 4294967296 then none else some {s with pc := target.toNat}
  | .ret => some {s with
      pc := (load32 s.core.memory (s.core.regs 4)).toNat
      core := put s.core 4 (s.core.regs 4 + (4#32))}
  | .compareRegister lhs rhs => some {s with flags := some (compare32 (s.core.regs lhs) rhs)}
  | .compareRegisters lhs rhs => some {s with flags := some (compare32 (s.core.regs lhs) (s.core.regs rhs))}
  | .storeImmediate a v => some {s with core := {s.core with memory := store32 s.core.memory (a.eval s.core.regs) v}}
  | .testMemoryByte a mask => some {s with flags := some (logical8 (s.core.memory (a.eval s.core.regs) &&& mask))}
  | .multiplyMemory dst a v => some {s with core := put s.core dst (load32 s.core.memory (a.eval s.core.regs) * v),flags := none}
  | .sar dst n => some {s with
      core := put s.core dst ((s.core.regs dst).sshiftRight (n.toNat % 32))
      flags := if n.toNat % 32 = 0 then s.flags else none}
  | .negateRegister dst => some {s with core := put s.core dst (-s.core.regs dst),flags := none}
  | .cdq => some {s with core := put s.core 2 (if (s.core.regs 0).toInt < 0 then BitVec.allOnes 32 else 0)}
  | .shld dst src n =>
      let count := n.toNat % 32
      some {s with
        core := put s.core dst (((s.core.regs dst ++ s.core.regs src) <<< count).extractLsb' 32 32)
        flags := if count = 0 then s.flags else none}
  | .setLess dst => do
      let flags ← s.flags
      some {s with core := putByte s.core dst (if flags.sign != flags.overflow then 1 else 0)}
  | .setGreater dst => do
      let flags ← s.flags
      some {s with core := putByte s.core dst (if !flags.lessEqual then 1 else 0)}
  -- IDIV truncates toward zero; zero divisors and out-of-range quotients fail.
  | .signedDivide src =>
      let dividend := (s.core.regs 2 ++ s.core.regs 0).toInt
      let divisor := (s.core.regs src).toInt
      let quotient := dividend.tdiv divisor
      if divisor = 0 ∨ quotient < -2147483648 ∨ 2147483647 < quotient then none
      else some {s with core := put (put s.core 0 (BitVec.ofInt 32 quotient)) 2 (BitVec.ofInt 32 (dividend.tmod divisor)), flags := none}
  | .jumpSigned condition offset => do
      let flags ← s.flags
      let take ← match condition with
        | 0 => some (flags.sign == flags.overflow)
        | 1 => some flags.lessEqual
        | 2 => some (!flags.lessEqual)
        | 3 => some (flags.sign != flags.overflow)
        | _ => none
      if take then
        let target := (s.pc : Int) + offset
        if target < 0 ∨ target ≥ 4294967296 then none else some {s with pc := target.toNat}
      else some s

abbrev Program := Nat → Option (Op × Nat)

def decodeAt (code : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (code.drop pc)).map (fun (op,rest) => (op,(code.drop pc).length-rest.length))

/-- An opt-in refinement of the existing decoder: register SUB retains its
ZF/SF/OF/CF projection. Older paths deliberately forget these flags and remain
valid conservative projections. This refinement depends only on decoded bytes,
never on an instruction address or an expected branch outcome. -/
def retainSubFlags : Op → Op
  | .control (.block (.arithmetic (.sub dst src))) => .subRegistersWithFlags dst src
  | op => op

def decodeAtWithSubFlags (code : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decodeAt code pc).map fun (op, size) => (retainSubFlags op, size)

/-- Retaining subtraction flags changes neither the arithmetic nor memory/PC. -/
theorem sub_flags_core (s : X86Control.State) (dst src : Reg) :
    (execute (.subRegistersWithFlags dst src) s).map (fun t => (t.core,t.pc)) =
    (execute (.control (.block (.arithmetic (.sub dst src)))) s).map
      (fun t => (t.core,t.pc)) := by rfl

def run (p : Program) (exits : List Nat) : Nat → X86Control.State → Option X86Control.State
  | fuel,s => if s.pc ∈ exits then some s else match fuel with
    | 0 => none
    | n+1 => do
      let (op,len) ← p s.pc
      let next ← execute op {s with pc := s.pc+len}
      run p exits n next

/-- A partial listing is accepted only on agreement with the byte decoder. -/
theorem run_sound (actual listed : Program)
    (sound : ∀ pc, listed pc ≠ none → actual pc = listed pc)
    (exits : List Nat) (fuel : Nat) (s : X86Control.State)
    (valid : run listed exits fuel s ≠ none) : run actual exits fuel s = run listed exits fuel s := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ n ih =>
    unfold run
    split
    · rfl
    · cases hp : listed s.pc with
      | none => simp [run,hp, *] at valid
      | some pair =>
        rw [sound s.pc (by simp [hp]),hp]
        rcases pair with ⟨op,len⟩
        dsimp only
        cases he : execute op {s with pc := s.pc+len} with
        | none => simp [he]
        | some next =>
          have hn : run listed exits n next ≠ none := by simpa [run,hp,he, *] using valid
          simpa [he] using ih next hn

inductive Prefix (program : Program) (exits : List Nat) : Nat → X86Control.State → X86Control.State → Prop
  | nil (s) : Prefix program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc = some (op, length))
      (executed : execute op {s with pc := s.pc + length} = some middle)
      (rest : Prefix program exits n middle last) :
      Prefix program exits (n+1) s last

/-- A proved prefix can be plugged into the rest of an execution, retaining the
same memory, registers, flags, PC, program and outer exit set at the seam. -/
theorem Prefix.run {program exits n s middle}
    (path : Prefix program exits n s middle) (fuel : Nat) :
    X86Routine.run program exits (n + fuel) s = X86Routine.run program exits fuel middle := by
  induction path with
  | nil => simp
  | @step n s middle last op length active decoded executed rest ih =>
    rw [Nat.succ_add]
    simpa only [X86Routine.run, active, ↓reduceIte, decoded, Bind.bind, Option.bind, executed] using ih


theorem run_mono {p exits n s t} (h : X86Routine.run p exits n s = some t) (extra : Nat) :
    X86Routine.run p exits (n + extra) s = some t := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86Routine.run,he] using h
      subst t
      unfold X86Routine.run
      simp [he]
    · simp [X86Routine.run, he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86Routine.run,he] using h
      subst t
      unfold X86Routine.run
      simp [he]
    · simp only [X86Routine.run, he, ↓reduceIte] at h
      cases hd : p s.pc with
      | none => simp [hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [hd,hx] at h
        | some next =>
          have hn : X86Routine.run p exits n next = some t := by simpa [hd,hx] using h
          simpa [X86Routine.run,he,hd,hx,Nat.succ_add] using ih hn

theorem run_path {p exits n s t} (h : X86Routine.run p exits n s = some t) :
    ∃ k, k ≤ n ∧ Prefix p exits k s t ∧ t.pc ∈ exits := by
  induction n generalizing s with
  | zero =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86Routine.run,he] using h
      subst t
      exact ⟨0,Nat.le_refl _,Prefix.nil s,he⟩
    · simp [X86Routine.run,he] at h
  | succ n ih =>
    by_cases he : s.pc ∈ exits
    · have ht : s = t := by simpa [X86Routine.run,he] using h
      subst t
      exact ⟨0,Nat.zero_le _,Prefix.nil s,he⟩
    · cases hd : p s.pc with
      | none => simp [X86Routine.run,he,hd] at h
      | some pair =>
        rcases pair with ⟨op,len⟩
        cases hx : execute op {s with pc := s.pc + len} with
        | none => simp [X86Routine.run,he,hd,hx] at h
        | some next =>
          have hn : X86Routine.run p exits n next = some t := by simpa [X86Routine.run,he,hd,hx] using h
          obtain ⟨k,hk,path,done⟩ := ih hn
          exact ⟨k+1,by omega,Prefix.step he hd hx path,done⟩

/-- Transfer a path into an enclosing program with a different exit set. Every
executed source instruction must agree and be outside the enclosing exits. -/
theorem Prefix.transfer {p exits n s t} (path : Prefix p exits n s t)
    (q : Program) (outer : List Nat)
    (agree : ∀ pc, p pc ≠ none → q pc = p pc)
    (active : ∀ pc, p pc ≠ none → pc ∉ outer) : Prefix q outer n s t := by
  induction path with
  | nil => exact Prefix.nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc ≠ none := by simp [hd]
    exact Prefix.step (active s.pc valid) ((agree s.pc valid).trans hd) hx ih

/-- Compose successful segments with a bound, even when a branch exits the
first segment early. No register, memory or flag reset occurs at the seam. -/
theorem Prefix.finish {p exits n s middle t} (path : Prefix p exits n s middle)
    {fuel : Nat} (tail : X86Routine.run p exits fuel middle = some t) (budget : Nat)
    (enough : n + fuel ≤ budget) : X86Routine.run p exits budget s = some t := by
  have joined : X86Routine.run p exits (n+fuel) s = some t := by rw [path.run fuel, tail]
  have lifted := run_mono joined (budget - (n+fuel))
  simpa only [Nat.add_sub_of_le enough] using lifted



end Doom.Verification.X86Routine
