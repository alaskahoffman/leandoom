import Doom.Proofs.InitializedE1M1
open Doom Doom.Proofs.InitializedE1M1
-- These are validator unit inputs, NOT captured DOS states.
example : stampCheck #[0,0] 1 = false := by decide +kernel
example : stampCheck (Array.replicate 475 0) 1 = true := by decide +kernel
example : stampCheck ((Array.replicate 475 0).set! 474 2) 1 = false := by decide +kernel
example : stampCheck (Array.replicate 475 0) 4294967294 = false := by decide +kernel
#check engine_inputs
#check started_inputs
#check fresh_pair
#print axioms Doom.Proofs.InitializedE1M1.engine_inputs
#print axioms Doom.Proofs.InitializedE1M1.fresh_pair
