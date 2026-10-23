import Doom.Proofs.E1M1AimQueryCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimProgramLink
open Verification

/-- Both old maps can be lifted unchanged exactly when decoded operations and
instruction lengths agree at every shared address. -/
def CompatibleAt (pc : Nat) : Prop :=
  X86ReturnCleanup.embed E1M1FirstIntercept.program pc=none ∨
  E1M1AimCompletedReturn.program pc=none ∨
  X86ReturnCleanup.embed E1M1FirstIntercept.program pc=E1M1AimCompletedReturn.program pc
instance (pc : Nat) : Decidable (CompatibleAt pc) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem region_0 : ∀ i : Fin 32, CompatibleAt (0x1d180+i.val) := by decide
theorem region_1 : ∀ i : Fin 32, CompatibleAt (0x1d1a0+i.val) := by decide
theorem region_2 : ∀ i : Fin 1, CompatibleAt (0x1d1c0+i.val) := by decide
theorem region_3 : ∀ i : Fin 32, CompatibleAt (0x26f60+i.val) := by decide
theorem region_4 : ∀ i : Fin 32, CompatibleAt (0x26f80+i.val) := by decide
theorem region_5 : ∀ i : Fin 32, CompatibleAt (0x26fa0+i.val) := by decide
theorem region_6 : ∀ i : Fin 32, CompatibleAt (0x26fc0+i.val) := by decide
theorem region_7 : ∀ i : Fin 32, CompatibleAt (0x26fe0+i.val) := by decide
theorem region_8 : ∀ i : Fin 26, CompatibleAt (0x27000+i.val) := by decide
theorem region_9 : ∀ i : Fin 30, CompatibleAt (0x27020+i.val) := by decide
theorem region_10 : ∀ i : Fin 32, CompatibleAt (0x2b760+i.val) := by decide
theorem region_11 : ∀ i : Fin 32, CompatibleAt (0x2b780+i.val) := by decide
theorem region_12 : ∀ i : Fin 32, CompatibleAt (0x2b7a0+i.val) := by decide
theorem region_13 : ∀ i : Fin 32, CompatibleAt (0x2b7c0+i.val) := by decide
theorem region_14 : ∀ i : Fin 32, CompatibleAt (0x2b7e0+i.val) := by decide
theorem region_15 : ∀ i : Fin 32, CompatibleAt (0x2b800+i.val) := by decide
theorem region_16 : ∀ i : Fin 32, CompatibleAt (0x2b820+i.val) := by decide
theorem region_17 : ∀ i : Fin 32, CompatibleAt (0x2b840+i.val) := by decide
theorem region_18 : ∀ i : Fin 32, CompatibleAt (0x2b860+i.val) := by decide
theorem region_19 : ∀ i : Fin 32, CompatibleAt (0x2b880+i.val) := by decide
theorem region_20 : ∀ i : Fin 32, CompatibleAt (0x2b8a0+i.val) := by decide
theorem region_21 : ∀ i : Fin 27, CompatibleAt (0x2b8c0+i.val) := by decide
theorem region_22 : ∀ i : Fin 32, CompatibleAt (0x2bb80+i.val) := by decide
theorem region_23 : ∀ i : Fin 32, CompatibleAt (0x2bba0+i.val) := by decide
theorem region_24 : ∀ i : Fin 32, CompatibleAt (0x2bbc0+i.val) := by decide
theorem region_25 : ∀ i : Fin 32, CompatibleAt (0x2bbe0+i.val) := by decide
theorem region_26 : ∀ i : Fin 25, CompatibleAt (0x2bc00+i.val) := by decide
theorem region_27 : ∀ i : Fin 32, CompatibleAt (0x2c010+i.val) := by decide
theorem region_28 : ∀ i : Fin 32, CompatibleAt (0x2c030+i.val) := by decide
theorem region_29 : ∀ i : Fin 32, CompatibleAt (0x2c050+i.val) := by decide
theorem region_30 : ∀ i : Fin 32, CompatibleAt (0x2c070+i.val) := by decide
theorem region_31 : ∀ i : Fin 32, CompatibleAt (0x2c090+i.val) := by decide
theorem region_32 : ∀ i : Fin 3, CompatibleAt (0x2c0b0+i.val) := by decide
theorem region_33 : ∀ i : Fin 32, CompatibleAt (0x2c1e0+i.val) := by decide
theorem region_34 : ∀ i : Fin 32, CompatibleAt (0x2c200+i.val) := by decide
theorem region_35 : ∀ i : Fin 32, CompatibleAt (0x2c220+i.val) := by decide
theorem region_36 : ∀ i : Fin 32, CompatibleAt (0x2c240+i.val) := by decide
theorem region_37 : ∀ i : Fin 32, CompatibleAt (0x2c260+i.val) := by decide
theorem region_38 : ∀ i : Fin 32, CompatibleAt (0x2c280+i.val) := by decide
theorem region_39 : ∀ i : Fin 7, CompatibleAt (0x2c2a0+i.val) := by decide
theorem region_40 : ∀ i : Fin 32, CompatibleAt (0x2c2d0+i.val) := by decide
theorem region_41 : ∀ i : Fin 32, CompatibleAt (0x2c2f0+i.val) := by decide
theorem region_42 : ∀ i : Fin 32, CompatibleAt (0x2c310+i.val) := by decide
theorem region_43 : ∀ i : Fin 4, CompatibleAt (0x2c330+i.val) := by decide
theorem region_44 : ∀ i : Fin 32, CompatibleAt (0x2c340+i.val) := by decide
theorem region_45 : ∀ i : Fin 32, CompatibleAt (0x2c360+i.val) := by decide
theorem region_46 : ∀ i : Fin 32, CompatibleAt (0x2c380+i.val) := by decide
theorem region_47 : ∀ i : Fin 10, CompatibleAt (0x2c3a0+i.val) := by decide
theorem region_48 : ∀ i : Fin 32, CompatibleAt (0x2c520+i.val) := by decide
theorem region_49 : ∀ i : Fin 32, CompatibleAt (0x2c540+i.val) := by decide
theorem region_50 : ∀ i : Fin 32, CompatibleAt (0x2c560+i.val) := by decide
theorem region_51 : ∀ i : Fin 17, CompatibleAt (0x2c580+i.val) := by decide
theorem region_52 : ∀ i : Fin 32, CompatibleAt (0x2c5a0+i.val) := by decide
theorem region_53 : ∀ i : Fin 32, CompatibleAt (0x2c5c0+i.val) := by decide
theorem region_54 : ∀ i : Fin 11, CompatibleAt (0x2c5e0+i.val) := by decide
theorem region_55 : ∀ i : Fin 32, CompatibleAt (0x2c5f0+i.val) := by decide
theorem region_56 : ∀ i : Fin 32, CompatibleAt (0x2c610+i.val) := by decide
theorem region_57 : ∀ i : Fin 32, CompatibleAt (0x2c630+i.val) := by decide
theorem region_58 : ∀ i : Fin 32, CompatibleAt (0x2c650+i.val) := by decide
theorem region_59 : ∀ i : Fin 32, CompatibleAt (0x2c670+i.val) := by decide
theorem region_60 : ∀ i : Fin 32, CompatibleAt (0x2c690+i.val) := by decide
theorem region_61 : ∀ i : Fin 32, CompatibleAt (0x2c6b0+i.val) := by decide
theorem region_62 : ∀ i : Fin 32, CompatibleAt (0x2c6d0+i.val) := by decide
theorem region_63 : ∀ i : Fin 32, CompatibleAt (0x2c6f0+i.val) := by decide
theorem region_64 : ∀ i : Fin 10, CompatibleAt (0x2c710+i.val) := by decide
theorem region_65 : ∀ i : Fin 32, CompatibleAt (0x2c720+i.val) := by decide
theorem region_66 : ∀ i : Fin 32, CompatibleAt (0x2c740+i.val) := by decide
theorem region_67 : ∀ i : Fin 32, CompatibleAt (0x2c760+i.val) := by decide
theorem region_68 : ∀ i : Fin 32, CompatibleAt (0x2c780+i.val) := by decide
theorem region_69 : ∀ i : Fin 32, CompatibleAt (0x2c7a0+i.val) := by decide
theorem region_70 : ∀ i : Fin 32, CompatibleAt (0x2c7c0+i.val) := by decide
theorem region_71 : ∀ i : Fin 32, CompatibleAt (0x2c7e0+i.val) := by decide
theorem region_72 : ∀ i : Fin 15, CompatibleAt (0x2c800+i.val) := by decide
theorem region_73 : ∀ i : Fin 32, CompatibleAt (0x2c810+i.val) := by decide
theorem region_74 : ∀ i : Fin 32, CompatibleAt (0x2c830+i.val) := by decide
theorem region_75 : ∀ i : Fin 32, CompatibleAt (0x2c850+i.val) := by decide
theorem region_76 : ∀ i : Fin 32, CompatibleAt (0x2c870+i.val) := by decide
theorem region_77 : ∀ i : Fin 10, CompatibleAt (0x2c890+i.val) := by decide
theorem region_78 : ∀ i : Fin 32, CompatibleAt (0x2c8a0+i.val) := by decide
theorem region_79 : ∀ i : Fin 32, CompatibleAt (0x2c8c0+i.val) := by decide
theorem region_80 : ∀ i : Fin 32, CompatibleAt (0x2c8e0+i.val) := by decide
theorem region_81 : ∀ i : Fin 32, CompatibleAt (0x2c900+i.val) := by decide
theorem region_82 : ∀ i : Fin 32, CompatibleAt (0x2c920+i.val) := by decide
theorem region_83 : ∀ i : Fin 32, CompatibleAt (0x2c940+i.val) := by decide
theorem region_84 : ∀ i : Fin 32, CompatibleAt (0x2c960+i.val) := by decide
theorem region_85 : ∀ i : Fin 32, CompatibleAt (0x2c980+i.val) := by decide
theorem region_86 : ∀ i : Fin 32, CompatibleAt (0x2c9a0+i.val) := by decide
theorem region_87 : ∀ i : Fin 32, CompatibleAt (0x2c9c0+i.val) := by decide
theorem region_88 : ∀ i : Fin 32, CompatibleAt (0x2c9e0+i.val) := by decide
theorem region_89 : ∀ i : Fin 32, CompatibleAt (0x2ca00+i.val) := by decide
theorem region_90 : ∀ i : Fin 32, CompatibleAt (0x2ca20+i.val) := by decide
theorem region_91 : ∀ i : Fin 32, CompatibleAt (0x2ca40+i.val) := by decide
theorem region_92 : ∀ i : Fin 32, CompatibleAt (0x2ca60+i.val) := by decide
theorem region_93 : ∀ i : Fin 32, CompatibleAt (0x2ca80+i.val) := by decide
theorem region_94 : ∀ i : Fin 32, CompatibleAt (0x2caa0+i.val) := by decide
theorem region_95 : ∀ i : Fin 32, CompatibleAt (0x2cac0+i.val) := by decide
theorem region_96 : ∀ i : Fin 32, CompatibleAt (0x2cae0+i.val) := by decide
theorem region_97 : ∀ i : Fin 20, CompatibleAt (0x2cb00+i.val) := by decide
theorem region_98 : ∀ i : Fin 32, CompatibleAt (0x2d176+i.val) := by decide
theorem region_99 : ∀ i : Fin 32, CompatibleAt (0x2d196+i.val) := by decide
theorem region_100 : ∀ i : Fin 32, CompatibleAt (0x2d1b6+i.val) := by decide
theorem region_101 : ∀ i : Fin 32, CompatibleAt (0x2d1d6+i.val) := by decide
theorem region_102 : ∀ i : Fin 32, CompatibleAt (0x2d1f6+i.val) := by decide
theorem region_103 : ∀ i : Fin 32, CompatibleAt (0x2d216+i.val) := by decide
theorem region_104 : ∀ i : Fin 32, CompatibleAt (0x2d236+i.val) := by decide
theorem region_105 : ∀ i : Fin 32, CompatibleAt (0x2d256+i.val) := by decide
theorem region_106 : ∀ i : Fin 32, CompatibleAt (0x2d276+i.val) := by decide
theorem region_107 : ∀ i : Fin 27, CompatibleAt (0x2d296+i.val) := by decide
theorem region_108 : ∀ i : Fin 32, CompatibleAt (0x2d2f0+i.val) := by decide
theorem region_109 : ∀ i : Fin 32, CompatibleAt (0x2d310+i.val) := by decide
theorem region_110 : ∀ i : Fin 32, CompatibleAt (0x2d330+i.val) := by decide
theorem region_111 : ∀ i : Fin 32, CompatibleAt (0x2d350+i.val) := by decide
theorem region_112 : ∀ i : Fin 32, CompatibleAt (0x2d370+i.val) := by decide
theorem region_113 : ∀ i : Fin 32, CompatibleAt (0x2d390+i.val) := by decide
theorem region_114 : ∀ i : Fin 32, CompatibleAt (0x2d3b0+i.val) := by decide
theorem region_115 : ∀ i : Fin 23, CompatibleAt (0x2d3d0+i.val) := by decide
theorem region_116 : ∀ i : Fin 32, CompatibleAt (0x2d410+i.val) := by decide
theorem region_117 : ∀ i : Fin 32, CompatibleAt (0x2d430+i.val) := by decide
theorem region_118 : ∀ i : Fin 3, CompatibleAt (0x2d450+i.val) := by decide
theorem region_119 : ∀ i : Fin 32, CompatibleAt (0x2d460+i.val) := by decide
theorem region_120 : ∀ i : Fin 13, CompatibleAt (0x2d480+i.val) := by decide
theorem region_121 : ∀ i : Fin 32, CompatibleAt (0x2d4d0+i.val) := by decide
theorem region_122 : ∀ i : Fin 32, CompatibleAt (0x2d4f0+i.val) := by decide
theorem region_123 : ∀ i : Fin 32, CompatibleAt (0x2d7c0+i.val) := by decide
theorem region_124 : ∀ i : Fin 32, CompatibleAt (0x2d7e0+i.val) := by decide
theorem region_125 : ∀ i : Fin 32, CompatibleAt (0x2d800+i.val) := by decide
theorem region_126 : ∀ i : Fin 3, CompatibleAt (0x2d820+i.val) := by decide
theorem region_127 : ∀ i : Fin 32, CompatibleAt (0x2d890+i.val) := by decide
theorem region_128 : ∀ i : Fin 32, CompatibleAt (0x2d8b0+i.val) := by decide
theorem region_129 : ∀ i : Fin 28, CompatibleAt (0x2d8d0+i.val) := by decide
theorem region_130 : ∀ i : Fin 32, CompatibleAt (0x2d910+i.val) := by decide
theorem region_131 : ∀ i : Fin 32, CompatibleAt (0x2d930+i.val) := by decide
theorem region_132 : ∀ i : Fin 29, CompatibleAt (0x2d950+i.val) := by decide
theorem region_133 : ∀ i : Fin 32, CompatibleAt (0x30ea0+i.val) := by decide
theorem region_134 : ∀ i : Fin 32, CompatibleAt (0x30ec0+i.val) := by decide
theorem region_135 : ∀ i : Fin 27, CompatibleAt (0x30ee0+i.val) := by decide
theorem region_136 : ∀ i : Fin 7, CompatibleAt (0x418d8+i.val) := by decide

attribute [local irreducible] E1M1AimCompletedReturn.program OriginalPathReturn.program OriginalPathReturn.bytesProgram E1M1AimCompletedReturn.legacy OriginalAimQuery.program OriginalAimQuery.bytesProgram E1M1AimTraversalReturn.program OriginalTraversalReturn.program OriginalTraversalReturn.bytesProgram E1M1AimActorSelect.program OriginalAimActorSelect.program OriginalAimActorSelect.bytesProgram E1M1AimActorBottom.program OriginalAimActorBottom.program OriginalAimActorBottom.bytesProgram E1M1AimActorReject.program OriginalAimActorReject.program OriginalAimActorReject.bytesProgram E1M1AimActorTop.program OriginalAimActorTop.program OriginalAimActorTop.bytesProgram E1M1AimActorSkip.program E1M1AimRepeatProgram.program E1M1AimResume.program E1M1AimWindow.program OriginalAimWindow.program OriginalAimWindow.bytesProgram E1M1AimCeiling.program OriginalAimCeiling.program OriginalAimCeiling.bytesProgram E1M1AimFloor.program OriginalAimFloor.program OriginalAimFloor.bytesProgram E1M1AimDistance.program OriginalAimDistance.program OriginalAimDistance.bytesProgram E1M1AimOpening.program OriginalAimOpening.program OriginalAimOpening.bytesProgram OriginalAimGuard.program OriginalAimGuard.bytesProgram E1M1NoiseOpening.program NoiseOpening.program NoiseOpening.bytesProgram E1M1NoiseTraversal.program NoiseTraversal.program NoiseTraversal.bytesProgram E1M1NoiseAlert.program NoiseAlert.program NoiseAlert.bytesProgram E1M1WeaponContinuation.program WeaponFallback.program WeaponFallback.bytesProgram E1M1WeaponFire.program WeaponAmmo.program WeaponAmmo.bytesProgram WeaponFire.program WeaponFire.bytesProgram E1M1WeaponReadyReset.program PainSetter.program PainSetter.bytesProgram E1M1WeaponReadyEntry.program WeaponReadyEntry.program WeaponReadyEntry.bytesProgram E1M1WeaponReadyGate.program WeaponReadyGate.program WeaponReadyGate.bytesProgram E1M1WeaponReady.program WeaponReady.program WeaponReady.bytesProgram WeaponRaise.program WeaponRaise.bytesProgram OriginalDivMemory.program OriginalDivMemory.bytesProgram OriginalInterceptGate.program OriginalInterceptGate.bytesProgram OriginalInterceptSetup.program OriginalInterceptSetup.bytesProgram OriginalInterceptMinimum.program OriginalInterceptMinimum.bytesProgram OriginalAimActorGuard.program OriginalAimActorGuard.bytesProgram E1M1FirstIntercept.program E1M1TraversalEntry.program E1M1FiringAdvance.program E1M1ThingReturn.program E1M1ThingFraction.program E1M1ThingCrossing.program E1M1ThingFirstSide.program E1M1ThingCallback.program E1M1ThingEntry.program E1M1LineFinish.program E1M1LineFraction.program E1M1LineSecondPoint.program E1M1DivlineSide.program E1M1LineSide.program E1M1LineInterceptEntry.program E1M1LineCell.program E1M1PathCell.program E1M1PathGridSetup.program E1M1PathIntercept.program E1M1PathXStep.program E1M1PathInit.program OriginalPathInit.program OriginalPathInit.bytesProgram E1M1AimSetup.program OriginalAimSetup.program OriginalAimSetup.bytesProgram E1M1AimQuery.program E1M1BulletAim.program OriginalBulletSlope.program OriginalBulletSlope.bytesProgram E1M1DischargeSetters.program OriginalWeaponDischarge.program OriginalWeaponDischarge.bytesProgram OriginalPathXStep.program OriginalAbs.program OriginalAbs.bytesProgram OriginalPathXStep.localProgram OriginalPathXStep.bytesProgram OriginalPathIntercept.program OriginalPathIntercept.bytesProgram OriginalPathYStep.program OriginalPathYStep.localProgram OriginalPathYStep.bytesProgram OriginalPathSecondIntercept.program OriginalPathSecondIntercept.bytesProgram OriginalPathCell.program OriginalPathCell.bytesProgram OriginalLineBounds.program OriginalLineBounds.bytesProgram OriginalLineCell.program OriginalLineCell.bytesProgram OriginalLineInterceptEntry.program OriginalLineInterceptEntry.bytesProgram OriginalLineSide.program OriginalLineSide.bytesProgram OriginalDivlineSide.program OriginalDivlineSide.bytesProgram OriginalLineSecondPoint.program OriginalLineSecondPoint.bytesProgram OriginalLineSecondPoint.localBytes OriginalLineFraction.program OriginalLineFraction.bytesProgram OriginalInterceptVector.program OriginalInterceptVector.bytesProgram OriginalLineFinish.program OriginalLineFinish.bytesProgram OriginalThingEntry.program OriginalThingEntry.bytesProgram OriginalThingCallback.program OriginalThingCallback.bytesProgram OriginalThingDiagonal.program OriginalThingDiagonal.bytesProgram OriginalThingSecondSide.localProgram OriginalThingSecondSide.bytesProgram OriginalThingFraction.program OriginalThingFraction.bytesProgram OriginalThingFinish.program OriginalThingFinish.bytesProgram OriginalPathAdvance.program OriginalPathAdvance.bytesProgram E1M1InterceptGate.program E1M1PspriteLight.program

/-- Outside the added regions both maps reduce to the same existing core. -/
theorem outside (pc : Nat)
    (h0 : ¬(0x1d180≤pc ∧ pc<0x1d1c1))
    (h1 : ¬(0x26f60≤pc ∧ pc<0x26fa6))
    (h2 : ¬(0x26fa6≤pc ∧ pc<0x2701a))
    (h3 : ¬(0x26fc4≤pc ∧ pc<0x26fee))
    (h4 : ¬(0x27020≤pc ∧ pc<0x2703e))
    (h5 : ¬(0x2b760≤pc ∧ pc<0x2b77f))
    (h6 : ¬(0x2b77f≤pc ∧ pc<0x2b797))
    (h7 : ¬(0x2b797≤pc ∧ pc<0x2b7a6))
    (h8 : ¬(0x2b7a6≤pc ∧ pc<0x2b7d1))
    (h9 : ¬(0x2b7d1≤pc ∧ pc<0x2b800))
    (h10 : ¬(0x2b800≤pc ∧ pc<0x2b81a))
    (h11 : ¬(0x2b81a≤pc ∧ pc<0x2b843))
    (h12 : ¬(0x2b843≤pc ∧ pc<0x2b875))
    (h13 : ¬(0x2b875≤pc ∧ pc<0x2b881))
    (h14 : ¬(0x2b881≤pc ∧ pc<0x2b89d))
    (h15 : ¬(0x2b89d≤pc ∧ pc<0x2b8a9))
    (h16 : ¬(0x2b8a9≤pc ∧ pc<0x2b8d2))
    (h17 : ¬(0x2b8d2≤pc ∧ pc<0x2b8db))
    (h18 : ¬(0x2bb80≤pc ∧ pc<0x2bba0))
    (h19 : ¬(0x2bba0≤pc ∧ pc<0x2bbff))
    (h20 : ¬(0x2bbff≤pc ∧ pc<0x2bc19))
    (h21 : ¬(0x2c010≤pc ∧ pc<0x2c0b3))
    (h22 : ¬(0x2c1e0≤pc ∧ pc<0x2c2a7))
    (h23 : ¬(0x2c2d0≤pc ∧ pc<0x2c334))
    (h24 : ¬(0x2c340≤pc ∧ pc<0x2c3aa))
    (h25 : ¬(0x2c520≤pc ∧ pc<0x2c541))
    (h26 : ¬(0x2c541≤pc ∧ pc<0x2c587))
    (h27 : ¬(0x2c587≤pc ∧ pc<0x2c591))
    (h28 : ¬(0x2c5a0≤pc ∧ pc<0x2c5c0))
    (h29 : ¬(0x2c5c0≤pc ∧ pc<0x2c5d2))
    (h30 : ¬(0x2c5d2≤pc ∧ pc<0x2c5e2))
    (h31 : ¬(0x2c5e2≤pc ∧ pc<0x2c5eb))
    (h32 : ¬(0x2c5f0≤pc ∧ pc<0x2c637))
    (h33 : ¬(0x2c637≤pc ∧ pc<0x2c64d))
    (h34 : ¬(0x2c64d≤pc ∧ pc<0x2c65f))
    (h35 : ¬(0x2c65f≤pc ∧ pc<0x2c691))
    (h36 : ¬(0x2c691≤pc ∧ pc<0x2c6bb))
    (h37 : ¬(0x2c6bb≤pc ∧ pc<0x2c71a))
    (h38 : ¬(0x2c711≤pc ∧ pc<0x2c71a))
    (h39 : ¬(0x2c720≤pc ∧ pc<0x2c72b))
    (h40 : ¬(0x2c72b≤pc ∧ pc<0x2c78d))
    (h41 : ¬(0x2c78d≤pc ∧ pc<0x2c7ae))
    (h42 : ¬(0x2c7ae≤pc ∧ pc<0x2c7da))
    (h43 : ¬(0x2c7da≤pc ∧ pc<0x2c80f))
    (h44 : ¬(0x2c810≤pc ∧ pc<0x2c841))
    (h45 : ¬(0x2c841≤pc ∧ pc<0x2c85e))
    (h46 : ¬(0x2c85e≤pc ∧ pc<0x2c887))
    (h47 : ¬(0x2c887≤pc ∧ pc<0x2c89a))
    (h48 : ¬(0x2c8a0≤pc ∧ pc<0x2c96c))
    (h49 : ¬(0x2c96c≤pc ∧ pc<0x2c9d3))
    (h50 : ¬(0x2c9d3≤pc ∧ pc<0x2ca10))
    (h51 : ¬(0x2ca10≤pc ∧ pc<0x2ca5f))
    (h52 : ¬(0x2ca5f≤pc ∧ pc<0x2ca7f))
    (h53 : ¬(0x2ca7f≤pc ∧ pc<0x2cab5))
    (h54 : ¬(0x2cab5≤pc ∧ pc<0x2cafd))
    (h55 : ¬(0x2cafd≤pc ∧ pc<0x2cb0b))
    (h56 : ¬(0x2cb0b≤pc ∧ pc<0x2cb11))
    (h57 : ¬(0x2cb11≤pc ∧ pc<0x2cb14))
    (h58 : ¬(0x2d176≤pc ∧ pc<0x2d19f))
    (h59 : ¬(0x2d19f≤pc ∧ pc<0x2d2b1))
    (h60 : ¬(0x2d2f0≤pc ∧ pc<0x2d333))
    (h61 : ¬(0x2d333≤pc ∧ pc<0x2d392))
    (h62 : ¬(0x2d392≤pc ∧ pc<0x2d3e7))
    (h63 : ¬(0x2d410≤pc ∧ pc<0x2d453))
    (h64 : ¬(0x2d460≤pc ∧ pc<0x2d48d))
    (h65 : ¬(0x2d4d0≤pc ∧ pc<0x2d510))
    (h66 : ¬(0x2d7c0≤pc ∧ pc<0x2d823))
    (h67 : ¬(0x2d890≤pc ∧ pc<0x2d8ec))
    (h68 : ¬(0x2d910≤pc ∧ pc<0x2d96d))
    (h69 : ¬(0x30ea0≤pc ∧ pc<0x30efb))
    (h70 : ¬(0x418d8≤pc ∧ pc<0x418df))
    : X86ReturnCleanup.embed E1M1FirstIntercept.program pc=E1M1AimCompletedReturn.program pc := by
  have e0 : OriginalInterceptGate.program pc=none := by
    simp only [OriginalInterceptGate.bytesProgram, OriginalInterceptGate.program, h46, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e1 : OriginalInterceptMinimum.program pc=none := by
    simp only [OriginalInterceptMinimum.bytesProgram, OriginalInterceptMinimum.program, h45, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e2 : E1M1InterceptGate.program pc=none := by
    simp only [E1M1InterceptGate.program, e0, e1, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e3 : PainSetter.program pc=none := by
    simp only [PainSetter.bytesProgram, PainSetter.program, h69, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e4 : DeathSetter.program pc=none := by
    simp only [DeathSetter.program, e3, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e5 : OriginalWeaponDischarge.program pc=none := by
    simp only [OriginalWeaponDischarge.bytesProgram, OriginalWeaponDischarge.program, h67, h68, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e6 : E1M1DischargeSetters.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1DischargeSetters.program, e4, e5, h67, h68, h69, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e7 : OriginalBulletSlope.program pc=none := by
    simp only [OriginalBulletSlope.bytesProgram, OriginalBulletSlope.program, h66, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e8 : E1M1BulletAim.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1BulletAim.program, e6, e7, h66, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e9 : OriginalAimQuery.program pc=none := by
    simp only [OriginalAimQuery.bytesProgram, OriginalAimQuery.program, h18, h20, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e10 : E1M1AimQuery.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimQuery.program, e8, e9, h18, h20, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e11 : OriginalAimSetup.program pc=none := by
    simp only [OriginalAimSetup.bytesProgram, OriginalAimSetup.program, h19, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e12 : E1M1AimSetup.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimSetup.program, e10, e11, h19, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e13 : OriginalPathInit.program pc=none := by
    simp only [OriginalPathInit.bytesProgram, OriginalPathInit.program, h48, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e14 : E1M1PathInit.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1PathInit.program, e12, e13, h48, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e15 : OriginalAbs.program pc=none := by
    simp only [OriginalAbs.bytesProgram, OriginalAbs.program, h70, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e16 : OriginalDivMemory.program pc=none := by
    simp only [OriginalDivMemory.bytesProgram, OriginalDivMemory.program, h0, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e17 : OriginalPathXStep.program pc=none := by
    simp only [OriginalPathXStep.bytesProgram, OriginalPathXStep.localProgram, OriginalPathXStep.program, e15, e16, h49, h70, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e18 : E1M1PathXStep.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1PathXStep.program, e14, e17, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e19 : OriginalPathIntercept.program pc=none := by
    simp only [OriginalPathIntercept.bytesProgram, OriginalPathIntercept.program, h50, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e20 : E1M1PathIntercept.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1PathIntercept.program, e18, e19, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e21 : OriginalPathSecondIntercept.program pc=none := by
    simp only [OriginalPathSecondIntercept.bytesProgram, OriginalPathSecondIntercept.program, h52, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e22 : OriginalPathYStep.program pc=none := by
    simp only [OriginalPathYStep.bytesProgram, OriginalPathYStep.localProgram, OriginalPathYStep.program, e15, e16, h51, h70, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e23 : E1M1PathGridSetup.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1PathGridSetup.program, e20, e21, e22, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e24 : OriginalLineBounds.program pc=none := by
    simp only [OriginalLineBounds.bytesProgram, OriginalLineBounds.program, h25, h27, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e25 : OriginalPathCell.program pc=none := by
    simp only [OriginalPathCell.bytesProgram, OriginalPathCell.program, h53, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e26 : E1M1PathCell.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1PathCell.program, e23, e24, e25, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e27 : OriginalLineCell.program pc=none := by
    simp only [OriginalLineCell.bytesProgram, OriginalLineCell.program, h26, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e28 : E1M1LineCell.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineCell.program, e26, e27, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e29 : OriginalLineInterceptEntry.program pc=none := by
    simp only [OriginalLineInterceptEntry.bytesProgram, OriginalLineInterceptEntry.program, h32, h34, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e30 : E1M1LineInterceptEntry.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineInterceptEntry.program, e28, e29, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e31 : OriginalLineSide.program pc=none := by
    simp only [OriginalLineSide.bytesProgram, OriginalLineSide.program, h21, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e32 : E1M1LineSide.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineSide.program, e30, e31, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e33 : OriginalDivlineSide.program pc=none := by
    simp only [OriginalDivlineSide.bytesProgram, OriginalDivlineSide.program, h22, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e34 : E1M1DivlineSide.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1DivlineSide.program, e32, e33, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e35 : OriginalLineSecondPoint.program pc=none := by
    simp only [OriginalLineSecondPoint.bytesProgram, OriginalLineSecondPoint.localBytes, OriginalLineSecondPoint.program, e33, e31, h33, h35, h38, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e36 : E1M1LineSecondPoint.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineSecondPoint.program, e34, e35, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e37 : OriginalInterceptVector.program pc=none := by
    simp only [OriginalInterceptVector.bytesProgram, OriginalInterceptVector.program, e16, h23, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e38 : OriginalLineFraction.program pc=none := by
    simp only [OriginalLineFraction.bytesProgram, OriginalLineFraction.program, e37, h36, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e39 : E1M1LineFraction.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineFraction.program, e36, e38, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e40 : OriginalLineFinish.program pc=none := by
    simp only [OriginalLineFinish.bytesProgram, OriginalLineFinish.program, h37, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e41 : E1M1LineFinish.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineFinish.program, e39, e40, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e42 : E1M1LineResume.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1LineResume.program, e41, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e43 : OriginalLineTail.program pc=E1M1PspriteLight.program pc := by
    simp only [OriginalLineTail.program, e42, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e44 : OriginalLineCrossing.program pc=E1M1PspriteLight.program pc := by
    simp only [OriginalLineCrossing.program, e43, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e45 : OriginalLineDispatch.program pc=E1M1PspriteLight.program pc := by
    simp only [OriginalLineDispatch.program, e44, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e46 : OriginalLineMixedInvariant.program pc=E1M1PspriteLight.program pc := by
    simp only [OriginalLineMixedInvariant.program, e45, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e47 : OriginalThingEntry.program pc=none := by
    simp only [OriginalThingEntry.bytesProgram, OriginalThingEntry.program, h28, h29, h31, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e48 : E1M1ThingEntry.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1ThingEntry.program, e46, e47, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e49 : OriginalThingCallback.program pc=none := by
    simp only [OriginalThingCallback.bytesProgram, OriginalThingCallback.program, h30, h39, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e50 : E1M1ThingCallback.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1ThingCallback.program, e48, e49, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e51 : OriginalThingDiagonal.program pc=none := by
    simp only [OriginalThingDiagonal.bytesProgram, OriginalThingDiagonal.program, h40, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e52 : E1M1ThingFirstSide.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1ThingCallback.program pc with
  | some op => some op
  | none => OriginalThingDiagonal.program pc) = E1M1PspriteLight.program pc
    rw [e50]
    simp only [e50, e51, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e53 : E1M1ThingCrossing.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1ThingFirstSide.program pc with
  | some op => some op
  | none => OriginalThingSecondSide.localProgram pc) = E1M1PspriteLight.program pc
    rw [e52]
    simp only [OriginalThingSecondSide.bytesProgram, OriginalThingSecondSide.localProgram, e52, h41, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e54 : OriginalThingFraction.program pc=none := by
    simp only [OriginalThingFraction.bytesProgram, OriginalThingFraction.program, e37, h42, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e55 : E1M1ThingFraction.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1ThingCrossing.program pc with
  | some op => some op
  | none => OriginalThingFraction.program pc) = E1M1PspriteLight.program pc
    rw [e53]
    simp only [e53, e54, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e56 : OriginalThingFinish.program pc=none := by
    simp only [OriginalThingFinish.bytesProgram, OriginalThingFinish.program, h43, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e57 : E1M1ThingReturn.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1ThingFraction.program pc with
  | some op => some op
  | none => OriginalThingFinish.program pc) = E1M1PspriteLight.program pc
    rw [e55]
    simp only [e55, e56, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e58 : E1M1ThingVisit.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1ThingVisit.program, e57, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e59 : E1M1ThingList.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1ThingList.program, e58, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e60 : E1M1ThingTraversal.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1ThingTraversal.program, e59, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e61 : E1M1FiringThings.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1FiringThings.program, e60, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e62 : E1M1FiringCellReturn.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1FiringCellReturn.program, e61, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e63 : OriginalPathAdvance.program pc=none := by
    simp only [OriginalPathAdvance.bytesProgram, OriginalPathAdvance.program, h54, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e64 : E1M1FiringAdvance.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1FiringCellReturn.program pc with
  | some op => some op
  | none => OriginalPathAdvance.program pc) = E1M1PspriteLight.program pc
    rw [e62]
    simp only [e62, e63, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e65 : OriginalInterceptSetup.program pc=none := by
    simp only [OriginalInterceptSetup.bytesProgram, OriginalInterceptSetup.program, h44, h55, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e66 : E1M1TraversalEntry.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1FiringAdvance.program pc with
  | some op => some op
  | none => OriginalInterceptSetup.program pc) = E1M1PspriteLight.program pc
    rw [e64]
    simp only [e64, e65, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e67 : E1M1FirstIntercept.program pc=E1M1PspriteLight.program pc := by
    with_unfolding_all change (match E1M1TraversalEntry.program pc with
  | some op => some op
  | none => E1M1InterceptGate.program pc) = E1M1PspriteLight.program pc
    rw [e66]
    simp only [e2, e66, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e68 : WeaponRaise.program pc=none := by
    simp only [WeaponRaise.bytesProgram, WeaponRaise.program, h65, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e69 : WeaponReady.program pc=none := by
    simp only [WeaponReady.bytesProgram, WeaponReady.program, h62, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e70 : E1M1WeaponReady.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponReady.program, e68, e69, h62, h65, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e71 : WeaponReadyGate.program pc=none := by
    simp only [WeaponReadyGate.bytesProgram, WeaponReadyGate.program, h61, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e72 : E1M1WeaponReadyGate.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponReadyGate.program, e70, e71, h61, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e73 : WeaponReadyEntry.program pc=none := by
    simp only [WeaponReadyEntry.bytesProgram, WeaponReadyEntry.program, h60, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e74 : E1M1WeaponReadyEntry.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponReadyEntry.program, e72, e73, h60, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e75 : E1M1WeaponReadyReset.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponReadyReset.program, e4, e74, h69, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e76 : WeaponAmmo.program pc=none := by
    simp only [WeaponAmmo.bytesProgram, WeaponAmmo.program, h58, h64, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e77 : WeaponFire.program pc=none := by
    simp only [WeaponFire.bytesProgram, WeaponFire.program, h63, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e78 : E1M1WeaponFire.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponFire.program, e75, e76, e77, h58, h63, h64, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e79 : WeaponFallback.program pc=none := by
    simp only [WeaponFallback.bytesProgram, WeaponFallback.program, h59, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e80 : E1M1WeaponContinuation.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1WeaponContinuation.program, e78, e79, h59, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e81 : NoiseAlert.program pc=none := by
    simp only [NoiseAlert.bytesProgram, NoiseAlert.program, h1, h4, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e82 : E1M1NoiseAlert.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1NoiseAlert.program, e80, e81, h1, h4, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e83 : NoiseTraversal.program pc=none := by
    simp only [NoiseTraversal.bytesProgram, NoiseTraversal.program, h2, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e84 : E1M1NoiseTraversal.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1NoiseTraversal.program, e82, e83, h2, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e85 : NoiseOpening.program pc=none := by
    simp only [NoiseOpening.bytesProgram, NoiseOpening.program, h3, h24, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e86 : E1M1NoiseOpening.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1NoiseOpening.program, e84, e85, h24, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e87 : OriginalAimGuard.program pc=none := by
    simp only [OriginalAimGuard.bytesProgram, OriginalAimGuard.program, h5, h17, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e88 : OriginalAimOpening.program pc=none := by
    simp only [OriginalAimOpening.bytesProgram, OriginalAimOpening.program, h6, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e89 : E1M1AimOpening.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimOpening.program, e86, e87, e88, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e90 : OriginalAimDistance.program pc=none := by
    simp only [OriginalAimDistance.bytesProgram, OriginalAimDistance.program, h7, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e91 : E1M1AimDistance.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimDistance.program, e89, e90, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e92 : OriginalAimFloor.program pc=none := by
    simp only [OriginalAimFloor.bytesProgram, OriginalAimFloor.program, h8, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e93 : E1M1AimFloor.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimFloor.program, e91, e92, e16, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e94 : OriginalAimCeiling.program pc=none := by
    simp only [OriginalAimCeiling.bytesProgram, OriginalAimCeiling.program, h9, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e95 : E1M1AimCeiling.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimCeiling.program, e93, e94, e16, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e96 : OriginalAimWindow.program pc=none := by
    simp only [OriginalAimWindow.bytesProgram, OriginalAimWindow.program, h10, h15, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e97 : E1M1AimWindow.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimWindow.program, e95, e96, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e98 : E1M1AimResume.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimResume.program, e97, e0, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e99 : E1M1AimRepeatProgram.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimRepeatProgram.program, e98, e1, e65, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e100 : OriginalAimActorGuard.program pc=none := by
    simp only [OriginalAimActorGuard.bytesProgram, OriginalAimActorGuard.program, e87, h11, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e101 : E1M1AimActorSkip.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimActorSkip.program, e99, e100, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e102 : OriginalAimActorTop.program pc=none := by
    simp only [OriginalAimActorTop.bytesProgram, OriginalAimActorTop.program, h12, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e103 : E1M1AimActorTop.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimActorTop.program, e101, e102, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e104 : OriginalAimActorReject.program pc=none := by
    simp only [OriginalAimActorReject.bytesProgram, OriginalAimActorReject.program, h13, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e105 : E1M1AimActorReject.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimActorReject.program, e103, e104, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e106 : OriginalAimActorBottom.program pc=none := by
    simp only [OriginalAimActorBottom.bytesProgram, OriginalAimActorBottom.program, h14, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e107 : E1M1AimActorBottom.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimActorBottom.program, e105, e106, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e108 : OriginalAimActorSelect.program pc=none := by
    simp only [OriginalAimActorSelect.bytesProgram, OriginalAimActorSelect.program, h16, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e109 : E1M1AimActorSelect.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimActorSelect.program, e107, e108, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e110 : OriginalTraversalReturn.program pc=none := by
    simp only [OriginalTraversalReturn.bytesProgram, OriginalTraversalReturn.program, h47, h56, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e111 : E1M1AimTraversalReturn.program pc=E1M1PspriteLight.program pc := by
    simp only [E1M1AimTraversalReturn.program, e109, e110, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e112 : OriginalPathReturn.program pc=none := by
    simp only [OriginalPathReturn.bytesProgram, OriginalPathReturn.program, h57, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  have e113 : E1M1AimCompletedReturn.program pc=X86ReturnCleanup.embed E1M1PspriteLight.program pc := by
    simp only [E1M1AimCompletedReturn.legacy, E1M1AimCompletedReturn.program, e111, e9, e112, if_false, false_or, or_false, ite_self, X86ReturnCleanup.embed, Option.map_none]
    all_goals cases E1M1PspriteLight.program pc <;> rfl
  rw [e113]
  simp only [X86ReturnCleanup.embed, e67]

/-- Exhaustive address compatibility, including undecodable addresses and the
unbounded complement of all added instruction regions. -/
theorem compatible (pc : Nat) : CompatibleAt pc := by
  by_cases r0 : 0x1d180≤pc ∧ pc<0x1d1a0
  · have eq : 0x1d180+(pc-0x1d180)=pc := by omega
    simpa only [eq] using region_0 ⟨pc-0x1d180,by omega⟩
  by_cases r1 : 0x1d1a0≤pc ∧ pc<0x1d1c0
  · have eq : 0x1d1a0+(pc-0x1d1a0)=pc := by omega
    simpa only [eq] using region_1 ⟨pc-0x1d1a0,by omega⟩
  by_cases r2 : 0x1d1c0≤pc ∧ pc<0x1d1c1
  · have eq : 0x1d1c0+(pc-0x1d1c0)=pc := by omega
    simpa only [eq] using region_2 ⟨pc-0x1d1c0,by omega⟩
  by_cases r3 : 0x26f60≤pc ∧ pc<0x26f80
  · have eq : 0x26f60+(pc-0x26f60)=pc := by omega
    simpa only [eq] using region_3 ⟨pc-0x26f60,by omega⟩
  by_cases r4 : 0x26f80≤pc ∧ pc<0x26fa0
  · have eq : 0x26f80+(pc-0x26f80)=pc := by omega
    simpa only [eq] using region_4 ⟨pc-0x26f80,by omega⟩
  by_cases r5 : 0x26fa0≤pc ∧ pc<0x26fc0
  · have eq : 0x26fa0+(pc-0x26fa0)=pc := by omega
    simpa only [eq] using region_5 ⟨pc-0x26fa0,by omega⟩
  by_cases r6 : 0x26fc0≤pc ∧ pc<0x26fe0
  · have eq : 0x26fc0+(pc-0x26fc0)=pc := by omega
    simpa only [eq] using region_6 ⟨pc-0x26fc0,by omega⟩
  by_cases r7 : 0x26fe0≤pc ∧ pc<0x27000
  · have eq : 0x26fe0+(pc-0x26fe0)=pc := by omega
    simpa only [eq] using region_7 ⟨pc-0x26fe0,by omega⟩
  by_cases r8 : 0x27000≤pc ∧ pc<0x2701a
  · have eq : 0x27000+(pc-0x27000)=pc := by omega
    simpa only [eq] using region_8 ⟨pc-0x27000,by omega⟩
  by_cases r9 : 0x27020≤pc ∧ pc<0x2703e
  · have eq : 0x27020+(pc-0x27020)=pc := by omega
    simpa only [eq] using region_9 ⟨pc-0x27020,by omega⟩
  by_cases r10 : 0x2b760≤pc ∧ pc<0x2b780
  · have eq : 0x2b760+(pc-0x2b760)=pc := by omega
    simpa only [eq] using region_10 ⟨pc-0x2b760,by omega⟩
  by_cases r11 : 0x2b780≤pc ∧ pc<0x2b7a0
  · have eq : 0x2b780+(pc-0x2b780)=pc := by omega
    simpa only [eq] using region_11 ⟨pc-0x2b780,by omega⟩
  by_cases r12 : 0x2b7a0≤pc ∧ pc<0x2b7c0
  · have eq : 0x2b7a0+(pc-0x2b7a0)=pc := by omega
    simpa only [eq] using region_12 ⟨pc-0x2b7a0,by omega⟩
  by_cases r13 : 0x2b7c0≤pc ∧ pc<0x2b7e0
  · have eq : 0x2b7c0+(pc-0x2b7c0)=pc := by omega
    simpa only [eq] using region_13 ⟨pc-0x2b7c0,by omega⟩
  by_cases r14 : 0x2b7e0≤pc ∧ pc<0x2b800
  · have eq : 0x2b7e0+(pc-0x2b7e0)=pc := by omega
    simpa only [eq] using region_14 ⟨pc-0x2b7e0,by omega⟩
  by_cases r15 : 0x2b800≤pc ∧ pc<0x2b820
  · have eq : 0x2b800+(pc-0x2b800)=pc := by omega
    simpa only [eq] using region_15 ⟨pc-0x2b800,by omega⟩
  by_cases r16 : 0x2b820≤pc ∧ pc<0x2b840
  · have eq : 0x2b820+(pc-0x2b820)=pc := by omega
    simpa only [eq] using region_16 ⟨pc-0x2b820,by omega⟩
  by_cases r17 : 0x2b840≤pc ∧ pc<0x2b860
  · have eq : 0x2b840+(pc-0x2b840)=pc := by omega
    simpa only [eq] using region_17 ⟨pc-0x2b840,by omega⟩
  by_cases r18 : 0x2b860≤pc ∧ pc<0x2b880
  · have eq : 0x2b860+(pc-0x2b860)=pc := by omega
    simpa only [eq] using region_18 ⟨pc-0x2b860,by omega⟩
  by_cases r19 : 0x2b880≤pc ∧ pc<0x2b8a0
  · have eq : 0x2b880+(pc-0x2b880)=pc := by omega
    simpa only [eq] using region_19 ⟨pc-0x2b880,by omega⟩
  by_cases r20 : 0x2b8a0≤pc ∧ pc<0x2b8c0
  · have eq : 0x2b8a0+(pc-0x2b8a0)=pc := by omega
    simpa only [eq] using region_20 ⟨pc-0x2b8a0,by omega⟩
  by_cases r21 : 0x2b8c0≤pc ∧ pc<0x2b8db
  · have eq : 0x2b8c0+(pc-0x2b8c0)=pc := by omega
    simpa only [eq] using region_21 ⟨pc-0x2b8c0,by omega⟩
  by_cases r22 : 0x2bb80≤pc ∧ pc<0x2bba0
  · have eq : 0x2bb80+(pc-0x2bb80)=pc := by omega
    simpa only [eq] using region_22 ⟨pc-0x2bb80,by omega⟩
  by_cases r23 : 0x2bba0≤pc ∧ pc<0x2bbc0
  · have eq : 0x2bba0+(pc-0x2bba0)=pc := by omega
    simpa only [eq] using region_23 ⟨pc-0x2bba0,by omega⟩
  by_cases r24 : 0x2bbc0≤pc ∧ pc<0x2bbe0
  · have eq : 0x2bbc0+(pc-0x2bbc0)=pc := by omega
    simpa only [eq] using region_24 ⟨pc-0x2bbc0,by omega⟩
  by_cases r25 : 0x2bbe0≤pc ∧ pc<0x2bc00
  · have eq : 0x2bbe0+(pc-0x2bbe0)=pc := by omega
    simpa only [eq] using region_25 ⟨pc-0x2bbe0,by omega⟩
  by_cases r26 : 0x2bc00≤pc ∧ pc<0x2bc19
  · have eq : 0x2bc00+(pc-0x2bc00)=pc := by omega
    simpa only [eq] using region_26 ⟨pc-0x2bc00,by omega⟩
  by_cases r27 : 0x2c010≤pc ∧ pc<0x2c030
  · have eq : 0x2c010+(pc-0x2c010)=pc := by omega
    simpa only [eq] using region_27 ⟨pc-0x2c010,by omega⟩
  by_cases r28 : 0x2c030≤pc ∧ pc<0x2c050
  · have eq : 0x2c030+(pc-0x2c030)=pc := by omega
    simpa only [eq] using region_28 ⟨pc-0x2c030,by omega⟩
  by_cases r29 : 0x2c050≤pc ∧ pc<0x2c070
  · have eq : 0x2c050+(pc-0x2c050)=pc := by omega
    simpa only [eq] using region_29 ⟨pc-0x2c050,by omega⟩
  by_cases r30 : 0x2c070≤pc ∧ pc<0x2c090
  · have eq : 0x2c070+(pc-0x2c070)=pc := by omega
    simpa only [eq] using region_30 ⟨pc-0x2c070,by omega⟩
  by_cases r31 : 0x2c090≤pc ∧ pc<0x2c0b0
  · have eq : 0x2c090+(pc-0x2c090)=pc := by omega
    simpa only [eq] using region_31 ⟨pc-0x2c090,by omega⟩
  by_cases r32 : 0x2c0b0≤pc ∧ pc<0x2c0b3
  · have eq : 0x2c0b0+(pc-0x2c0b0)=pc := by omega
    simpa only [eq] using region_32 ⟨pc-0x2c0b0,by omega⟩
  by_cases r33 : 0x2c1e0≤pc ∧ pc<0x2c200
  · have eq : 0x2c1e0+(pc-0x2c1e0)=pc := by omega
    simpa only [eq] using region_33 ⟨pc-0x2c1e0,by omega⟩
  by_cases r34 : 0x2c200≤pc ∧ pc<0x2c220
  · have eq : 0x2c200+(pc-0x2c200)=pc := by omega
    simpa only [eq] using region_34 ⟨pc-0x2c200,by omega⟩
  by_cases r35 : 0x2c220≤pc ∧ pc<0x2c240
  · have eq : 0x2c220+(pc-0x2c220)=pc := by omega
    simpa only [eq] using region_35 ⟨pc-0x2c220,by omega⟩
  by_cases r36 : 0x2c240≤pc ∧ pc<0x2c260
  · have eq : 0x2c240+(pc-0x2c240)=pc := by omega
    simpa only [eq] using region_36 ⟨pc-0x2c240,by omega⟩
  by_cases r37 : 0x2c260≤pc ∧ pc<0x2c280
  · have eq : 0x2c260+(pc-0x2c260)=pc := by omega
    simpa only [eq] using region_37 ⟨pc-0x2c260,by omega⟩
  by_cases r38 : 0x2c280≤pc ∧ pc<0x2c2a0
  · have eq : 0x2c280+(pc-0x2c280)=pc := by omega
    simpa only [eq] using region_38 ⟨pc-0x2c280,by omega⟩
  by_cases r39 : 0x2c2a0≤pc ∧ pc<0x2c2a7
  · have eq : 0x2c2a0+(pc-0x2c2a0)=pc := by omega
    simpa only [eq] using region_39 ⟨pc-0x2c2a0,by omega⟩
  by_cases r40 : 0x2c2d0≤pc ∧ pc<0x2c2f0
  · have eq : 0x2c2d0+(pc-0x2c2d0)=pc := by omega
    simpa only [eq] using region_40 ⟨pc-0x2c2d0,by omega⟩
  by_cases r41 : 0x2c2f0≤pc ∧ pc<0x2c310
  · have eq : 0x2c2f0+(pc-0x2c2f0)=pc := by omega
    simpa only [eq] using region_41 ⟨pc-0x2c2f0,by omega⟩
  by_cases r42 : 0x2c310≤pc ∧ pc<0x2c330
  · have eq : 0x2c310+(pc-0x2c310)=pc := by omega
    simpa only [eq] using region_42 ⟨pc-0x2c310,by omega⟩
  by_cases r43 : 0x2c330≤pc ∧ pc<0x2c334
  · have eq : 0x2c330+(pc-0x2c330)=pc := by omega
    simpa only [eq] using region_43 ⟨pc-0x2c330,by omega⟩
  by_cases r44 : 0x2c340≤pc ∧ pc<0x2c360
  · have eq : 0x2c340+(pc-0x2c340)=pc := by omega
    simpa only [eq] using region_44 ⟨pc-0x2c340,by omega⟩
  by_cases r45 : 0x2c360≤pc ∧ pc<0x2c380
  · have eq : 0x2c360+(pc-0x2c360)=pc := by omega
    simpa only [eq] using region_45 ⟨pc-0x2c360,by omega⟩
  by_cases r46 : 0x2c380≤pc ∧ pc<0x2c3a0
  · have eq : 0x2c380+(pc-0x2c380)=pc := by omega
    simpa only [eq] using region_46 ⟨pc-0x2c380,by omega⟩
  by_cases r47 : 0x2c3a0≤pc ∧ pc<0x2c3aa
  · have eq : 0x2c3a0+(pc-0x2c3a0)=pc := by omega
    simpa only [eq] using region_47 ⟨pc-0x2c3a0,by omega⟩
  by_cases r48 : 0x2c520≤pc ∧ pc<0x2c540
  · have eq : 0x2c520+(pc-0x2c520)=pc := by omega
    simpa only [eq] using region_48 ⟨pc-0x2c520,by omega⟩
  by_cases r49 : 0x2c540≤pc ∧ pc<0x2c560
  · have eq : 0x2c540+(pc-0x2c540)=pc := by omega
    simpa only [eq] using region_49 ⟨pc-0x2c540,by omega⟩
  by_cases r50 : 0x2c560≤pc ∧ pc<0x2c580
  · have eq : 0x2c560+(pc-0x2c560)=pc := by omega
    simpa only [eq] using region_50 ⟨pc-0x2c560,by omega⟩
  by_cases r51 : 0x2c580≤pc ∧ pc<0x2c591
  · have eq : 0x2c580+(pc-0x2c580)=pc := by omega
    simpa only [eq] using region_51 ⟨pc-0x2c580,by omega⟩
  by_cases r52 : 0x2c5a0≤pc ∧ pc<0x2c5c0
  · have eq : 0x2c5a0+(pc-0x2c5a0)=pc := by omega
    simpa only [eq] using region_52 ⟨pc-0x2c5a0,by omega⟩
  by_cases r53 : 0x2c5c0≤pc ∧ pc<0x2c5e0
  · have eq : 0x2c5c0+(pc-0x2c5c0)=pc := by omega
    simpa only [eq] using region_53 ⟨pc-0x2c5c0,by omega⟩
  by_cases r54 : 0x2c5e0≤pc ∧ pc<0x2c5eb
  · have eq : 0x2c5e0+(pc-0x2c5e0)=pc := by omega
    simpa only [eq] using region_54 ⟨pc-0x2c5e0,by omega⟩
  by_cases r55 : 0x2c5f0≤pc ∧ pc<0x2c610
  · have eq : 0x2c5f0+(pc-0x2c5f0)=pc := by omega
    simpa only [eq] using region_55 ⟨pc-0x2c5f0,by omega⟩
  by_cases r56 : 0x2c610≤pc ∧ pc<0x2c630
  · have eq : 0x2c610+(pc-0x2c610)=pc := by omega
    simpa only [eq] using region_56 ⟨pc-0x2c610,by omega⟩
  by_cases r57 : 0x2c630≤pc ∧ pc<0x2c650
  · have eq : 0x2c630+(pc-0x2c630)=pc := by omega
    simpa only [eq] using region_57 ⟨pc-0x2c630,by omega⟩
  by_cases r58 : 0x2c650≤pc ∧ pc<0x2c670
  · have eq : 0x2c650+(pc-0x2c650)=pc := by omega
    simpa only [eq] using region_58 ⟨pc-0x2c650,by omega⟩
  by_cases r59 : 0x2c670≤pc ∧ pc<0x2c690
  · have eq : 0x2c670+(pc-0x2c670)=pc := by omega
    simpa only [eq] using region_59 ⟨pc-0x2c670,by omega⟩
  by_cases r60 : 0x2c690≤pc ∧ pc<0x2c6b0
  · have eq : 0x2c690+(pc-0x2c690)=pc := by omega
    simpa only [eq] using region_60 ⟨pc-0x2c690,by omega⟩
  by_cases r61 : 0x2c6b0≤pc ∧ pc<0x2c6d0
  · have eq : 0x2c6b0+(pc-0x2c6b0)=pc := by omega
    simpa only [eq] using region_61 ⟨pc-0x2c6b0,by omega⟩
  by_cases r62 : 0x2c6d0≤pc ∧ pc<0x2c6f0
  · have eq : 0x2c6d0+(pc-0x2c6d0)=pc := by omega
    simpa only [eq] using region_62 ⟨pc-0x2c6d0,by omega⟩
  by_cases r63 : 0x2c6f0≤pc ∧ pc<0x2c710
  · have eq : 0x2c6f0+(pc-0x2c6f0)=pc := by omega
    simpa only [eq] using region_63 ⟨pc-0x2c6f0,by omega⟩
  by_cases r64 : 0x2c710≤pc ∧ pc<0x2c71a
  · have eq : 0x2c710+(pc-0x2c710)=pc := by omega
    simpa only [eq] using region_64 ⟨pc-0x2c710,by omega⟩
  by_cases r65 : 0x2c720≤pc ∧ pc<0x2c740
  · have eq : 0x2c720+(pc-0x2c720)=pc := by omega
    simpa only [eq] using region_65 ⟨pc-0x2c720,by omega⟩
  by_cases r66 : 0x2c740≤pc ∧ pc<0x2c760
  · have eq : 0x2c740+(pc-0x2c740)=pc := by omega
    simpa only [eq] using region_66 ⟨pc-0x2c740,by omega⟩
  by_cases r67 : 0x2c760≤pc ∧ pc<0x2c780
  · have eq : 0x2c760+(pc-0x2c760)=pc := by omega
    simpa only [eq] using region_67 ⟨pc-0x2c760,by omega⟩
  by_cases r68 : 0x2c780≤pc ∧ pc<0x2c7a0
  · have eq : 0x2c780+(pc-0x2c780)=pc := by omega
    simpa only [eq] using region_68 ⟨pc-0x2c780,by omega⟩
  by_cases r69 : 0x2c7a0≤pc ∧ pc<0x2c7c0
  · have eq : 0x2c7a0+(pc-0x2c7a0)=pc := by omega
    simpa only [eq] using region_69 ⟨pc-0x2c7a0,by omega⟩
  by_cases r70 : 0x2c7c0≤pc ∧ pc<0x2c7e0
  · have eq : 0x2c7c0+(pc-0x2c7c0)=pc := by omega
    simpa only [eq] using region_70 ⟨pc-0x2c7c0,by omega⟩
  by_cases r71 : 0x2c7e0≤pc ∧ pc<0x2c800
  · have eq : 0x2c7e0+(pc-0x2c7e0)=pc := by omega
    simpa only [eq] using region_71 ⟨pc-0x2c7e0,by omega⟩
  by_cases r72 : 0x2c800≤pc ∧ pc<0x2c80f
  · have eq : 0x2c800+(pc-0x2c800)=pc := by omega
    simpa only [eq] using region_72 ⟨pc-0x2c800,by omega⟩
  by_cases r73 : 0x2c810≤pc ∧ pc<0x2c830
  · have eq : 0x2c810+(pc-0x2c810)=pc := by omega
    simpa only [eq] using region_73 ⟨pc-0x2c810,by omega⟩
  by_cases r74 : 0x2c830≤pc ∧ pc<0x2c850
  · have eq : 0x2c830+(pc-0x2c830)=pc := by omega
    simpa only [eq] using region_74 ⟨pc-0x2c830,by omega⟩
  by_cases r75 : 0x2c850≤pc ∧ pc<0x2c870
  · have eq : 0x2c850+(pc-0x2c850)=pc := by omega
    simpa only [eq] using region_75 ⟨pc-0x2c850,by omega⟩
  by_cases r76 : 0x2c870≤pc ∧ pc<0x2c890
  · have eq : 0x2c870+(pc-0x2c870)=pc := by omega
    simpa only [eq] using region_76 ⟨pc-0x2c870,by omega⟩
  by_cases r77 : 0x2c890≤pc ∧ pc<0x2c89a
  · have eq : 0x2c890+(pc-0x2c890)=pc := by omega
    simpa only [eq] using region_77 ⟨pc-0x2c890,by omega⟩
  by_cases r78 : 0x2c8a0≤pc ∧ pc<0x2c8c0
  · have eq : 0x2c8a0+(pc-0x2c8a0)=pc := by omega
    simpa only [eq] using region_78 ⟨pc-0x2c8a0,by omega⟩
  by_cases r79 : 0x2c8c0≤pc ∧ pc<0x2c8e0
  · have eq : 0x2c8c0+(pc-0x2c8c0)=pc := by omega
    simpa only [eq] using region_79 ⟨pc-0x2c8c0,by omega⟩
  by_cases r80 : 0x2c8e0≤pc ∧ pc<0x2c900
  · have eq : 0x2c8e0+(pc-0x2c8e0)=pc := by omega
    simpa only [eq] using region_80 ⟨pc-0x2c8e0,by omega⟩
  by_cases r81 : 0x2c900≤pc ∧ pc<0x2c920
  · have eq : 0x2c900+(pc-0x2c900)=pc := by omega
    simpa only [eq] using region_81 ⟨pc-0x2c900,by omega⟩
  by_cases r82 : 0x2c920≤pc ∧ pc<0x2c940
  · have eq : 0x2c920+(pc-0x2c920)=pc := by omega
    simpa only [eq] using region_82 ⟨pc-0x2c920,by omega⟩
  by_cases r83 : 0x2c940≤pc ∧ pc<0x2c960
  · have eq : 0x2c940+(pc-0x2c940)=pc := by omega
    simpa only [eq] using region_83 ⟨pc-0x2c940,by omega⟩
  by_cases r84 : 0x2c960≤pc ∧ pc<0x2c980
  · have eq : 0x2c960+(pc-0x2c960)=pc := by omega
    simpa only [eq] using region_84 ⟨pc-0x2c960,by omega⟩
  by_cases r85 : 0x2c980≤pc ∧ pc<0x2c9a0
  · have eq : 0x2c980+(pc-0x2c980)=pc := by omega
    simpa only [eq] using region_85 ⟨pc-0x2c980,by omega⟩
  by_cases r86 : 0x2c9a0≤pc ∧ pc<0x2c9c0
  · have eq : 0x2c9a0+(pc-0x2c9a0)=pc := by omega
    simpa only [eq] using region_86 ⟨pc-0x2c9a0,by omega⟩
  by_cases r87 : 0x2c9c0≤pc ∧ pc<0x2c9e0
  · have eq : 0x2c9c0+(pc-0x2c9c0)=pc := by omega
    simpa only [eq] using region_87 ⟨pc-0x2c9c0,by omega⟩
  by_cases r88 : 0x2c9e0≤pc ∧ pc<0x2ca00
  · have eq : 0x2c9e0+(pc-0x2c9e0)=pc := by omega
    simpa only [eq] using region_88 ⟨pc-0x2c9e0,by omega⟩
  by_cases r89 : 0x2ca00≤pc ∧ pc<0x2ca20
  · have eq : 0x2ca00+(pc-0x2ca00)=pc := by omega
    simpa only [eq] using region_89 ⟨pc-0x2ca00,by omega⟩
  by_cases r90 : 0x2ca20≤pc ∧ pc<0x2ca40
  · have eq : 0x2ca20+(pc-0x2ca20)=pc := by omega
    simpa only [eq] using region_90 ⟨pc-0x2ca20,by omega⟩
  by_cases r91 : 0x2ca40≤pc ∧ pc<0x2ca60
  · have eq : 0x2ca40+(pc-0x2ca40)=pc := by omega
    simpa only [eq] using region_91 ⟨pc-0x2ca40,by omega⟩
  by_cases r92 : 0x2ca60≤pc ∧ pc<0x2ca80
  · have eq : 0x2ca60+(pc-0x2ca60)=pc := by omega
    simpa only [eq] using region_92 ⟨pc-0x2ca60,by omega⟩
  by_cases r93 : 0x2ca80≤pc ∧ pc<0x2caa0
  · have eq : 0x2ca80+(pc-0x2ca80)=pc := by omega
    simpa only [eq] using region_93 ⟨pc-0x2ca80,by omega⟩
  by_cases r94 : 0x2caa0≤pc ∧ pc<0x2cac0
  · have eq : 0x2caa0+(pc-0x2caa0)=pc := by omega
    simpa only [eq] using region_94 ⟨pc-0x2caa0,by omega⟩
  by_cases r95 : 0x2cac0≤pc ∧ pc<0x2cae0
  · have eq : 0x2cac0+(pc-0x2cac0)=pc := by omega
    simpa only [eq] using region_95 ⟨pc-0x2cac0,by omega⟩
  by_cases r96 : 0x2cae0≤pc ∧ pc<0x2cb00
  · have eq : 0x2cae0+(pc-0x2cae0)=pc := by omega
    simpa only [eq] using region_96 ⟨pc-0x2cae0,by omega⟩
  by_cases r97 : 0x2cb00≤pc ∧ pc<0x2cb14
  · have eq : 0x2cb00+(pc-0x2cb00)=pc := by omega
    simpa only [eq] using region_97 ⟨pc-0x2cb00,by omega⟩
  by_cases r98 : 0x2d176≤pc ∧ pc<0x2d196
  · have eq : 0x2d176+(pc-0x2d176)=pc := by omega
    simpa only [eq] using region_98 ⟨pc-0x2d176,by omega⟩
  by_cases r99 : 0x2d196≤pc ∧ pc<0x2d1b6
  · have eq : 0x2d196+(pc-0x2d196)=pc := by omega
    simpa only [eq] using region_99 ⟨pc-0x2d196,by omega⟩
  by_cases r100 : 0x2d1b6≤pc ∧ pc<0x2d1d6
  · have eq : 0x2d1b6+(pc-0x2d1b6)=pc := by omega
    simpa only [eq] using region_100 ⟨pc-0x2d1b6,by omega⟩
  by_cases r101 : 0x2d1d6≤pc ∧ pc<0x2d1f6
  · have eq : 0x2d1d6+(pc-0x2d1d6)=pc := by omega
    simpa only [eq] using region_101 ⟨pc-0x2d1d6,by omega⟩
  by_cases r102 : 0x2d1f6≤pc ∧ pc<0x2d216
  · have eq : 0x2d1f6+(pc-0x2d1f6)=pc := by omega
    simpa only [eq] using region_102 ⟨pc-0x2d1f6,by omega⟩
  by_cases r103 : 0x2d216≤pc ∧ pc<0x2d236
  · have eq : 0x2d216+(pc-0x2d216)=pc := by omega
    simpa only [eq] using region_103 ⟨pc-0x2d216,by omega⟩
  by_cases r104 : 0x2d236≤pc ∧ pc<0x2d256
  · have eq : 0x2d236+(pc-0x2d236)=pc := by omega
    simpa only [eq] using region_104 ⟨pc-0x2d236,by omega⟩
  by_cases r105 : 0x2d256≤pc ∧ pc<0x2d276
  · have eq : 0x2d256+(pc-0x2d256)=pc := by omega
    simpa only [eq] using region_105 ⟨pc-0x2d256,by omega⟩
  by_cases r106 : 0x2d276≤pc ∧ pc<0x2d296
  · have eq : 0x2d276+(pc-0x2d276)=pc := by omega
    simpa only [eq] using region_106 ⟨pc-0x2d276,by omega⟩
  by_cases r107 : 0x2d296≤pc ∧ pc<0x2d2b1
  · have eq : 0x2d296+(pc-0x2d296)=pc := by omega
    simpa only [eq] using region_107 ⟨pc-0x2d296,by omega⟩
  by_cases r108 : 0x2d2f0≤pc ∧ pc<0x2d310
  · have eq : 0x2d2f0+(pc-0x2d2f0)=pc := by omega
    simpa only [eq] using region_108 ⟨pc-0x2d2f0,by omega⟩
  by_cases r109 : 0x2d310≤pc ∧ pc<0x2d330
  · have eq : 0x2d310+(pc-0x2d310)=pc := by omega
    simpa only [eq] using region_109 ⟨pc-0x2d310,by omega⟩
  by_cases r110 : 0x2d330≤pc ∧ pc<0x2d350
  · have eq : 0x2d330+(pc-0x2d330)=pc := by omega
    simpa only [eq] using region_110 ⟨pc-0x2d330,by omega⟩
  by_cases r111 : 0x2d350≤pc ∧ pc<0x2d370
  · have eq : 0x2d350+(pc-0x2d350)=pc := by omega
    simpa only [eq] using region_111 ⟨pc-0x2d350,by omega⟩
  by_cases r112 : 0x2d370≤pc ∧ pc<0x2d390
  · have eq : 0x2d370+(pc-0x2d370)=pc := by omega
    simpa only [eq] using region_112 ⟨pc-0x2d370,by omega⟩
  by_cases r113 : 0x2d390≤pc ∧ pc<0x2d3b0
  · have eq : 0x2d390+(pc-0x2d390)=pc := by omega
    simpa only [eq] using region_113 ⟨pc-0x2d390,by omega⟩
  by_cases r114 : 0x2d3b0≤pc ∧ pc<0x2d3d0
  · have eq : 0x2d3b0+(pc-0x2d3b0)=pc := by omega
    simpa only [eq] using region_114 ⟨pc-0x2d3b0,by omega⟩
  by_cases r115 : 0x2d3d0≤pc ∧ pc<0x2d3e7
  · have eq : 0x2d3d0+(pc-0x2d3d0)=pc := by omega
    simpa only [eq] using region_115 ⟨pc-0x2d3d0,by omega⟩
  by_cases r116 : 0x2d410≤pc ∧ pc<0x2d430
  · have eq : 0x2d410+(pc-0x2d410)=pc := by omega
    simpa only [eq] using region_116 ⟨pc-0x2d410,by omega⟩
  by_cases r117 : 0x2d430≤pc ∧ pc<0x2d450
  · have eq : 0x2d430+(pc-0x2d430)=pc := by omega
    simpa only [eq] using region_117 ⟨pc-0x2d430,by omega⟩
  by_cases r118 : 0x2d450≤pc ∧ pc<0x2d453
  · have eq : 0x2d450+(pc-0x2d450)=pc := by omega
    simpa only [eq] using region_118 ⟨pc-0x2d450,by omega⟩
  by_cases r119 : 0x2d460≤pc ∧ pc<0x2d480
  · have eq : 0x2d460+(pc-0x2d460)=pc := by omega
    simpa only [eq] using region_119 ⟨pc-0x2d460,by omega⟩
  by_cases r120 : 0x2d480≤pc ∧ pc<0x2d48d
  · have eq : 0x2d480+(pc-0x2d480)=pc := by omega
    simpa only [eq] using region_120 ⟨pc-0x2d480,by omega⟩
  by_cases r121 : 0x2d4d0≤pc ∧ pc<0x2d4f0
  · have eq : 0x2d4d0+(pc-0x2d4d0)=pc := by omega
    simpa only [eq] using region_121 ⟨pc-0x2d4d0,by omega⟩
  by_cases r122 : 0x2d4f0≤pc ∧ pc<0x2d510
  · have eq : 0x2d4f0+(pc-0x2d4f0)=pc := by omega
    simpa only [eq] using region_122 ⟨pc-0x2d4f0,by omega⟩
  by_cases r123 : 0x2d7c0≤pc ∧ pc<0x2d7e0
  · have eq : 0x2d7c0+(pc-0x2d7c0)=pc := by omega
    simpa only [eq] using region_123 ⟨pc-0x2d7c0,by omega⟩
  by_cases r124 : 0x2d7e0≤pc ∧ pc<0x2d800
  · have eq : 0x2d7e0+(pc-0x2d7e0)=pc := by omega
    simpa only [eq] using region_124 ⟨pc-0x2d7e0,by omega⟩
  by_cases r125 : 0x2d800≤pc ∧ pc<0x2d820
  · have eq : 0x2d800+(pc-0x2d800)=pc := by omega
    simpa only [eq] using region_125 ⟨pc-0x2d800,by omega⟩
  by_cases r126 : 0x2d820≤pc ∧ pc<0x2d823
  · have eq : 0x2d820+(pc-0x2d820)=pc := by omega
    simpa only [eq] using region_126 ⟨pc-0x2d820,by omega⟩
  by_cases r127 : 0x2d890≤pc ∧ pc<0x2d8b0
  · have eq : 0x2d890+(pc-0x2d890)=pc := by omega
    simpa only [eq] using region_127 ⟨pc-0x2d890,by omega⟩
  by_cases r128 : 0x2d8b0≤pc ∧ pc<0x2d8d0
  · have eq : 0x2d8b0+(pc-0x2d8b0)=pc := by omega
    simpa only [eq] using region_128 ⟨pc-0x2d8b0,by omega⟩
  by_cases r129 : 0x2d8d0≤pc ∧ pc<0x2d8ec
  · have eq : 0x2d8d0+(pc-0x2d8d0)=pc := by omega
    simpa only [eq] using region_129 ⟨pc-0x2d8d0,by omega⟩
  by_cases r130 : 0x2d910≤pc ∧ pc<0x2d930
  · have eq : 0x2d910+(pc-0x2d910)=pc := by omega
    simpa only [eq] using region_130 ⟨pc-0x2d910,by omega⟩
  by_cases r131 : 0x2d930≤pc ∧ pc<0x2d950
  · have eq : 0x2d930+(pc-0x2d930)=pc := by omega
    simpa only [eq] using region_131 ⟨pc-0x2d930,by omega⟩
  by_cases r132 : 0x2d950≤pc ∧ pc<0x2d96d
  · have eq : 0x2d950+(pc-0x2d950)=pc := by omega
    simpa only [eq] using region_132 ⟨pc-0x2d950,by omega⟩
  by_cases r133 : 0x30ea0≤pc ∧ pc<0x30ec0
  · have eq : 0x30ea0+(pc-0x30ea0)=pc := by omega
    simpa only [eq] using region_133 ⟨pc-0x30ea0,by omega⟩
  by_cases r134 : 0x30ec0≤pc ∧ pc<0x30ee0
  · have eq : 0x30ec0+(pc-0x30ec0)=pc := by omega
    simpa only [eq] using region_134 ⟨pc-0x30ec0,by omega⟩
  by_cases r135 : 0x30ee0≤pc ∧ pc<0x30efb
  · have eq : 0x30ee0+(pc-0x30ee0)=pc := by omega
    simpa only [eq] using region_135 ⟨pc-0x30ee0,by omega⟩
  by_cases r136 : 0x418d8≤pc ∧ pc<0x418df
  · have eq : 0x418d8+(pc-0x418d8)=pc := by omega
    simpa only [eq] using region_136 ⟨pc-0x418d8,by omega⟩
  exact Or.inr (Or.inr (outside pc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))

/-- Union of the two authenticated maps. Priority cannot change any decoded
operation or its length because `compatible` proves agreement on overlap. -/
def program : X86ReturnCleanup.Program := fun pc =>
  match E1M1AimCompletedReturn.program pc with
  | some op => some op
  | none => X86ReturnCleanup.embed E1M1FirstIntercept.program pc

theorem contains_return (pc : Nat) (present : E1M1AimCompletedReturn.program pc≠none) :
    program pc=E1M1AimCompletedReturn.program pc := by
  unfold program
  cases eq : E1M1AimCompletedReturn.program pc <;> simp_all

theorem contains_query (pc : Nat)
    (present : X86ReturnCleanup.embed E1M1FirstIntercept.program pc≠none) :
    program pc=X86ReturnCleanup.embed E1M1FirstIntercept.program pc := by
  rcases compatible pc with absent|absent|same
  · exact False.elim (present absent)
  · simp only [program,absent]
  · unfold program
    rw [←same]
    cases eq : X86ReturnCleanup.embed E1M1FirstIntercept.program pc <;> rfl

/-- Join the actual two prefixes without changing any state, code memory,
exit set, decoded instruction, or step count. -/
theorem append (cm : X86Memory.Memory) (exits : List Nat)
    (n m : Nat) (start middle finish : X86Control.State)
    (query : X86CodeMemory.Prefix cm E1M1FirstIntercept.program exits n start middle)
    (returned : X86ReturnCleanup.Prefix cm E1M1AimCompletedReturn.program exits m middle finish) :
    X86ReturnCleanup.Prefix cm program exits (n+m) start finish := by
  exact ((X86ReturnCleanup.lift query).transfer program contains_query).trans
    (returned.transfer program contains_return)
end Doom.Proofs.E1M1AimProgramLink
