import Lean
import TorusFourierNS.Basic
import TorusFourierNS.Heat
import TorusFourierNS.Strain
import TorusFourierNS
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : Array Name := #[`TorusFourierNS.Basic, `TorusFourierNS.Heat, `TorusFourierNS.Strain, `TorusFourierNS]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless targets.contains mod do continue
    unless ci matches .thmInfo _ do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let axStr := String.intercalate "," (axs.toList.map toString)
    IO.println s!"TA	{mod}	{n}	{axStr}"
