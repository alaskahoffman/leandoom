theorem joined_checked (s : X86Memory.State) (f : Option Flags) (rng : DoomRandom)
    (h : E1M1DeathReturn.Inputs s rng) :
    X86Routine.run E1M1DeathReturn.program [0x2a6b1] 26 ⟨s,f,0x2a3f1⟩=some (E1M1DeathReturn.result s rng) ∧
    (E1M1DeathReturn.result s rng).pc=0x2a6b1 ∧
    (E1M1DeathReturn.result s rng).core.memory=(DeathTiming.result s rng.play).core.memory ∧
    (E1M1DeathReturn.result s rng).core.regs 4=s.regs 4+24 ∧
    (E1M1DeathReturn.result s rng).core.regs 0=0 ∧
    (E1M1DeathReturn.result s rng).core.regs 2=s.regs 2 ∧
    (E1M1DeathReturn.result s rng).core.regs 5=load32 s.memory (s.regs 4) ∧
    (E1M1DeathReturn.result s rng).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (E1M1DeathReturn.result s rng).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (E1M1DeathReturn.result s rng).core.regs 1=load32 s.memory (s.regs 4+12) ∧
    (E1M1DeathReturn.result s rng).core.regs 3=load32 s.memory (s.regs 4+16) ∧
    (E1M1DeathReturn.result s rng).flags=some (compare32 0 1) ∧
    load32 (E1M1DeathReturn.result s rng).core.memory (0x1271c#32)=load32 s.memory (0x1271c#32) ∧
    PlayerHeight.Frame s.memory (E1M1DeathReturn.result s rng).core.memory (DeathTiming.writes s) :=
  E1M1DeathReturn.joined_execution s f rng h
