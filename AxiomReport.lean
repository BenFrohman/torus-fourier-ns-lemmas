/-
Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0.
Axiom report. Run: `lake env lean AxiomReport.lean`.
Prints `#print axioms`-equivalent output for every theorem in the `TorusFourierNS` module tree
and fails if any declaration there depends on an axiom other than
propext, Classical.choice, Quot.sound (for example `sorryAx`).
-/
import Lean
import TorusFourierNS

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array String := #[]
  let mut bad : Array String := #[]
  let mut nDecl := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`TorusFourierNS).isPrefixOf mod do continue
    if n.isInternal then continue
    nDecl := nDecl + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless allowed.contains a do bad := bad.push s!"{n} uses {a}"
    if ci matches .thmInfo _ then
      let ax := ", ".intercalate ((axs.toList.map toString).toArray.qsort (· < ·)).toList
      rows := rows.push s!"AXROW | `{n}` | `{mod}` | {if ax.isEmpty then "(none)" else ax} |"
  for r in rows.qsort (· < ·) do
    logInfo r
  logInfo s!"AXSUMMARY {rows.size} theorems, {nDecl} declarations in TorusFourierNS; nonstandard: {bad.size}"
  unless bad.isEmpty do
    throwError m!"AxiomReport FAIL:\n{"\n".intercalate bad.toList}"
