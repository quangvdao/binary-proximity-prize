/-
Environment and axiom audit for the protected IRS benchmark contract.

Run after building the full public library and baselines:
`lake env lean scripts/check-axioms.lean`.
-/
import ProximityPrize

open Lean Lean.Meta

def trustedModulePrefixes : List String :=
  ["Init", "Lean", "Lake", "Std", "Batteries", "Aesop", "Qq", "Plausible", "Cslib",
   "ProofWidgets", "ImportGraph", "LeanSearchClient", "Mathlib", "ArkLib",
   "VCVio", "CompPoly", "PolyFun", "Loom", "ToMathlib", "ProximityPrize"]

open Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut badMods : Array Name := #[]
  for m in mods do
    let top := (m.components.head?.getD m).toString
    unless trustedModulePrefixes.contains top do
      badMods := badMods.push m
  unless badMods.isEmpty do
    for m in badMods do
      IO.eprintln s!"::error::module `{m}` has an unreviewed top-level prefix"
    throwError "unreviewed modules in environment ({badMods.size})"

  let mut bad : Array (Name × Name) := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := mods[idx.toNat]!
      if (`ProximityPrize).isPrefixOf modName && ci.isAxiom then
        bad := bad.push (name, modName)
  unless bad.isEmpty do
    for (n, m) in bad do
      IO.eprintln s!"::error::axiom declaration `{n}` in module `{m}`"
    throwError "axiom declarations found in ProximityPrize modules ({bad.size})"
  IO.println "ok — reviewed module prefixes; no local axiom declarations"

open Elab.Command in
run_cmd liftTermElabM do
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mods := env.header.moduleNames
  let trustedDecls := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => if (`ProximityPrize).isPrefixOf mods[idx.toNat]! then some name else none
    | none => none
  for decl in trustedDecls do
    let axioms ← collectAxioms decl
    let offending := axioms.toList.filter (fun a => !whitelist.contains a)
    unless offending.isEmpty do
      for ax in offending do
        IO.eprintln s!"::error::trusted declaration `{decl}` depends on `{ax}`"
      throwError "binary profile and baseline closure has non-whitelisted axioms"
  IO.println "ok — binary profile and baseline closure uses only propext/Classical.choice/Quot.sound"
