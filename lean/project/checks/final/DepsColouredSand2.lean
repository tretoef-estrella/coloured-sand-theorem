import RequestProject.StringsAll.All
import RequestProject.TwoTheoremI.All
import RequestProject.ThmGTwo.All
import RequestProject.Strings.All
import RequestProject.Splitting.All
import RequestProject.TheoremB.All
import RequestProject.Exponent.All
import RequestProject.NumberOfFactors.All
import RequestProject.Corollaries.All
import RequestProject.Blocks.All
import RequestProject.Glue.All
import RequestProject.ThmH.All
import RequestProject.ThmG.All
import RequestProject.OddTheoremI.All
import RequestProject.OddSmith.All
import RequestProject.OddTotal.All

/-! Dependency cone of the headline theorems of «The Coloured Sand Theorem» (v3 + Theorems I, TOTAL + the three cases CSX1–3; Grepy Ship, 15 Oct 2026, version 2).
Grepy Ship, 14 October 2026; modelled on the cube's `DepsCubo2.lean`. For each headline theorem: the number of
project declarations (modules `RequestProject.*`) in its transitive cone, and how many come from each module.
The last command gives the union cone of all headline theorems together. -/

open Lean Elab Command
partial def collect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    for c in ci.getUsedConstantsAsSet.toList do
      acc := collect env c acc
    return acc

def report (env : Environment) (s : NameSet) (title : String) : CommandElabM Unit := do
  let mut mods : Std.HashMap Name Nat := {}
  let mut total := 0
  for n in s.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        total := total + 1
        mods := mods.insert m (mods.getD m 0 + 1)
    | none => pure ()
  logInfo m!"{title}: project decls in cone: {total}; modules: {mods.size}"
  for (m, c) in mods.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"{m} {c}"

elab "#deps " id:ident : command => do
  let env ← getEnv
  report env (collect env id.getId {}) id.getId.toString

elab "#depsall " ids:ident* : command => do
  let env ← getEnv
  let mut s : NameSet := {}
  for i in ids do
    s := collect env i.getId s
  report env s "UNION"

#deps ColouredSand.Splitting.theorem_A
#deps ColouredSand.TheoremB.theorem_B
#deps ColouredSand.Exponent.theorem_C
#deps ColouredSand.NumberOfFactors.theorem_D
#deps ColouredSand.NumberOfFactors.wilson_diagonal_form
#deps ColouredSand.Strings.theorem_E
#deps ColouredSand.ThmG.F1
#deps ColouredSand.ThmG.F2
#deps ColouredSand.ThmG.T1
#deps ColouredSand.ThmG.T2
#deps ColouredSand.ThmG.S1
#deps ColouredSand.ThmG.S2
#deps ColouredSand.ThmH.T4
#deps ColouredSand.ThmH.T5
#deps ColouredSand.Corollaries.corollary1_whole
#deps ColouredSand.Corollaries.corollary6
#deps ColouredSand.Glue.G2_glue_forced
#deps ColouredSand.Blocks.B1
#deps ColouredSand.OddTwist.theorem_I
#deps ColouredSand.OddTwist.theorem_I_invariant
#deps ColouredSand.OddTwist.oddTotal_S1
#deps ColouredSand.OddTwist.oddTotal_S2
#deps ColouredSand.Strings.strAll_theorem_E
#deps ColouredSand.TwoI.twoI_theorem_I
#deps ColouredSand.ThmGTwo.twoThmG
#deps ColouredSand.ThmGTwo.twoT1_allPrimes
#deps ColouredSand.ThmGTwo.twoT2_allPrimes
#deps ColouredSand.ThmGTwo.twoF1_allPrimes
#deps ColouredSand.ThmGTwo.twoF2_allPrimes
#deps ColouredSand.ThmGTwo.twoS1_allPrimes
#deps ColouredSand.ThmGTwo.twoS2_allPrimes
#depsall ColouredSand.Splitting.theorem_A ColouredSand.TheoremB.theorem_B ColouredSand.Exponent.theorem_C ColouredSand.NumberOfFactors.theorem_D ColouredSand.NumberOfFactors.wilson_diagonal_form ColouredSand.Strings.theorem_E ColouredSand.ThmG.F1 ColouredSand.ThmG.F2 ColouredSand.ThmG.T1 ColouredSand.ThmG.T2 ColouredSand.ThmG.S1 ColouredSand.ThmG.S2 ColouredSand.ThmH.T4 ColouredSand.ThmH.T5 ColouredSand.Corollaries.corollary1_whole ColouredSand.Corollaries.corollary6 ColouredSand.Glue.G2_glue_forced ColouredSand.Blocks.B1 ColouredSand.OddTwist.theorem_I ColouredSand.OddTwist.theorem_I_invariant ColouredSand.OddTwist.oddTotal_S1 ColouredSand.OddTwist.oddTotal_S2 ColouredSand.Strings.strAll_theorem_E ColouredSand.TwoI.twoI_theorem_I ColouredSand.ThmGTwo.twoThmG ColouredSand.ThmGTwo.twoT1_allPrimes ColouredSand.ThmGTwo.twoT2_allPrimes ColouredSand.ThmGTwo.twoF1_allPrimes ColouredSand.ThmGTwo.twoF2_allPrimes ColouredSand.ThmGTwo.twoS1_allPrimes ColouredSand.ThmGTwo.twoS2_allPrimes
