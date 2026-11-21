module

import all A1
import all BCor
import all Construct
import all DirBase
import all DirMain
import all FamGen
import all Found
import all Lower
import all LowerPadic
import all M2AxisSwap
import all M2BlockS
import all M2Closures
import all M2ConstructO
import all M2FilterD
import all M2Frobenius
import all M2GapG
import all M2Parity
import all M2Polymath
import all M2ResultM
import all M2ResultN
import all M2Tables
import all M2Ternary
import all M2TheoremL
import all M2ThetaJ
import all M2ThetaJ2
import all M2TupleN
import all M2WitnessK
import all Moment
import all MomentZ
import all MuShift
import all RingO
import all Slice
import all Summatory
import all Twist
import all TwistO
import all Upper

@[expose] public section

/-!
Axiom audit for the whole M2Polymath development: every declaration in the M2 modules (and the six
library modules they build on) may use only propext, Classical.choice and Quot.sound. Building this
file prints the count of declarations scanned and the number of nonstandard axiom uses (expected 0).
-/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List Name := [`A1, `BCor, `Construct, `FamGen, `M2AxisSwap, `M2BlockS, `M2Closures, `M2ConstructO, `M2FilterD, `M2Frobenius, `M2GapG, `M2Parity, `M2Polymath, `M2ResultM, `M2ResultN, `M2Tables, `M2Ternary, `M2TheoremL, `M2ThetaJ, `M2ThetaJ2, `M2TupleN, `M2WitnessK, `Moment, `MomentZ, `MuShift, `RingO, `Slice, `Summatory, `Twist, `TwistO, `Found, `Upper, `Lower, `LowerPadic, `DirBase, `DirMain]
  let mut bad := 0
  let mut tot := 0
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some i =>
      if mods.contains env.header.moduleNames[i.toNat]! then
        tot := tot + 1
        for a in (← collectAxioms n) do
          if a != ``propext && a != ``Classical.choice && a != ``Quot.sound then
            IO.println s!"{n} uses {a}"; bad := bad + 1
    | none => pure ()
  IO.println s!"declarations scanned: {tot}; nonstandard axiom uses: {bad}"
