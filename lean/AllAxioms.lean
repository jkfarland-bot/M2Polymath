import A1
import BCor
import Construct
import DirBase
import DirMain
import FamGen
import Found
import Lower
import LowerPadic
import M2AxisSwap
import M2BlockS
import M2Closures
import M2ConstructO
import M2FilterD
import M2Frobenius
import M2GapG
import M2Parity
import M2Polymath
import M2ResultM
import M2ResultN
import M2Tables
import M2Ternary
import M2TheoremL
import M2ThetaJ
import M2ThetaJ2
import M2TupleN
import M2WitnessK
import Moment
import MomentZ
import MuShift
import RingO
import Slice
import Summatory
import Twist
import TwistO
import Upper
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
