import WeightedShift
import AnalyticRadius
import PeriodicStability
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "BTP." || (name.toString.splitOn ".BTP.").length > 1 || name.toString.startsWith "PBFStability." || (name.toString.splitOn ".PBFStability.").length > 1 then
      if info.isTheorem then
        count := count + 1
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axs.toList}"
  logInfo m!"TOTAL_THEOREMS {count}: only propext, Classical.choice, Quot.sound"
