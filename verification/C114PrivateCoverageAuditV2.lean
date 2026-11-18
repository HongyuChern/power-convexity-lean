import PowerConvexity.Analysis.ActualUniformNormalSourceCorrectionFour
import PowerConvexity.Analysis.ActualUniformPositiveHarnackFour
import Lean
import Lean.Util.CollectAxioms

/-! # Minimal explicit coverage check for the two private C114 theorems

Version 2: replace the Lean 4.33.1 reserved token `matches` used as a local variable
in the first audit file. The original failed file and actual failure log are preserved.
Preparation alone is not a successful run.
The source inventory found exactly these two private theorems among the
291 new project modules. This file locates their actual internal names,
checks their transitive axioms, and asserts four concrete reachability edges
from already audited public theorems. It does not modify project proofs.

Reflection APIs were checked in the frozen Lean 4.33.1 sources:
Lean/PrivateName.lean, Lean/Util/CollectAxioms.lean and the use of
Environment.constants.toList in Lean/Elab/DocString/Builtin.lean.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Meta

namespace C114PrivateCoverageAudit

private def locatePrivateTheorem (userName : Name) : MetaM Name := do
  let env := (← getEnv).setExporting false
  let foundNames := env.constants.toList.filterMap fun (n, _) =>
    if isPrivateName n && privateToUserName n == userName then some n else none
  match foundNames with
  | [n] =>
    match ← getConstInfo n with
    | .thmInfo _ => return n
    | _ => throwError "Expected a private theorem for {userName}, found {n}."
  | _ => throwError "Expected exactly one private theorem for {userName}, found {foundNames}."

/-- The same type-and-value traversal as the cumulative C114 audit. -/
private def projectDependencies (root : Name) : MetaM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if !seen.contains c then
      seen := seen.insert c
      let ci ← getConstInfo c
      let vals := match ci with
        | .defnInfo v => #[v.type,v.value]
        | .thmInfo v => #[v.type,v.value]
        | .opaqueInfo v => #[v.type,v.value]
        | _ => #[ci.type]
      for e in vals do
        for d in e.getUsedConstants do
          if (d.toString.startsWith "PowerConvexity." ||
              d.toString.startsWith "_private.PowerConvexity.") && !seen.contains d then
            todo := todo.push d
  return seen

#eval show MetaM Unit from do
  let checks : Array (Name × Array Name) := #[
    (`PowerConvexity.normal_source_quadratic_symmetric_four, #[
      ``PowerConvexity.actual_normal_source_barrier_contDiff_four,
      ``PowerConvexity.actual_normal_source_barrier_derivative_four,
      ``PowerConvexity.actual_normal_source_barrier_hessian_four]),
    (`PowerConvexity.harnack_continuous_order_of_ae_four, #[
      ``PowerConvexity.actual_bounded_nonnegative_weak_harnack_four])]
  let mut checkedHelpers : Nat := 0
  let mut checkedEdges : Nat := 0
  for (userName, publicRoots) in checks do
    let helper ← locatePrivateTheorem userName
    let axioms ← collectAxioms helper
    let bad := axioms.filter fun n =>
      !(n == `propext || n == `Classical.choice || n == `Quot.sound)
    unless bad.isEmpty do
      throwError "Forbidden transitive axioms for {helper}: {bad}"
    logInfo m!"PASS: private theorem {helper}; allowed transitive axioms {axioms}."
    checkedHelpers := checkedHelpers + 1
    for publicRoot in publicRoots do
      let deps ← projectDependencies publicRoot
      unless deps.contains helper do
        throwError "Private theorem {helper} is not reachable from audited public root {publicRoot}."
      logInfo m!"PASS: {helper} is reachable from {publicRoot}; {deps.size} project dependencies."
      checkedEdges := checkedEdges + 1
  unless checkedHelpers == 2 && checkedEdges == 4 do
    throwError "Incomplete private coverage: {checkedHelpers} helpers and {checkedEdges} edges."
  logInfo "PASS: both private C114 theorems have allowed transitive axioms and all four public-root reachability edges."

end C114PrivateCoverageAudit
