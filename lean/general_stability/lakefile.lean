import Lake
open Lake DSL

package BTPGeneralStability

/-- Prepare the pinned dependencies, rebuild the project, and audit its axioms. -/
@[default_target]
target verify pkg : Unit := Job.sync do
  let env := #[("BTP_LEAN_BIN", some (← getLean).toString),
               ("BTP_LEANTAR", some (← getLeantar).toString)]
  for (cmd, fileName) in [("python3", "bootstrap.py"), ("sh", "check.sh")] do
    let child ← IO.Process.spawn { cmd, args := #[fileName], cwd := pkg.dir, env }
    let code ← child.wait
    unless code == 0 do
      error s!"{cmd} {fileName} exited with code {code}"
