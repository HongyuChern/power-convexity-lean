import PowerConvexityComparator.Problem
import PowerConvexity.Targets.ActualOriginalRouteMainTheorem
import Lean

/-! # Independent answer to the unchanged frozen problem through the original route

No old comparator solution is imported.  The closure-jet and Wirtinger
identifications are constructed directly from the frozen problem definitions.
The final answer has exactly Problem.MainStatement as its type.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexityComparator.OriginalRoute
open CHS.Calculus PowerConvexity

theorem freshClosedC2ToJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {u : E → ℝ} (h : Problem.ClosedC2 u U) :
    Nonempty (ClosureC2Jet u U) := by
  obtain ⟨D,H,hu,hD,hH,hDu,hHu⟩ := h
  exact ⟨{
    derivative := D
    hessian := H
    continuous_value := hu
    continuous_derivative := hD
    continuous_hessian := hH
    derivative_eq := hDu
    hessian_eq := hHu }⟩

theorem freshMixedHessianTwo
    {u : Problem.CTwo → ℝ} {x : Problem.CTwo} (hu : ContDiffAt ℝ 2 u x) :
    complexHessian standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j) u x=
      Problem.mixedHessianTwo u x := by
  ext i j
  rw [complexHessian_real_entry hu standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) i j]
  simp only [Problem.mixedHessianTwo,Problem.realAxis,Problem.imaginaryAxis,realHessian,
    standardComplexTwoBasis_apply]

theorem newMainAnswer : Problem.MainStatement := by
  intro U hU hbounded hstrict hsmooth u hu4 hclosed hzero hpositive hdet
  apply actual_original_route_mainTheorem hU hbounded hstrict hsmooth hu4
    (freshClosedC2ToJet hclosed) hzero
  · intro x hx
    rw [freshMixedHessianTwo ((hu4.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hpositive x hx
  · intro x hx
    rw [freshMixedHessianTwo ((hu4.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hdet x hx

#print Problem.MainStatement
#check @newMainAnswer
#check @PowerConvexity.actual_original_route_mainTheorem
#print axioms Problem.StrictDomain
#print axioms Problem.SmoothBoundary
#print axioms Problem.ClosedC2
#print axioms Problem.CTwo
#print axioms Problem.realAxis
#print axioms Problem.imaginaryAxis
#print axioms Problem.mixedHessianTwo
#print axioms Problem.MainStatement
#print axioms freshClosedC2ToJet
#print axioms freshMixedHessianTwo
#print axioms newMainAnswer
#print axioms PowerConvexity.actual_original_route_mainTheorem

open Lean Meta
set_option maxHeartbeats 0

private def newRouteProjectDependencies (root : Name) : MetaM (Std.HashSet Name) := do
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
          let s := d.toString
          if (s.startsWith "PowerConvexity." || s.startsWith "_private.PowerConvexity." ||
              s.startsWith "PowerConvexityComparator." || s.startsWith "_private.PowerConvexityComparator." ||
              s.startsWith "CHS." || s.startsWith "_private.CHS.") && !seen.contains d then
            todo := todo.push d
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  if env.contains `PowerConvexityComparator.Solution.mainAnswer then
    throwError "The old comparator Solution.mainAnswer is present in the imported environment."
  logInfo "PASS: the old comparator solution is absent from the imported environment."
  for root in #[``freshClosedC2ToJet,``freshMixedHessianTwo,``newMainAnswer,
      ``PowerConvexity.actual_original_route_mainTheorem] do
    let deps ← newRouteProjectDependencies root
    let bad := deps.toArray.filter fun n =>
      let s := n.toString
      s == "PowerConvexity.mainTheorem" ||
      s == "PowerConvexity.mainTwo_geometric_target_strict_chord" ||
      s == "PowerConvexity.mainTwo_geometric_target_positive_realHessian" ||
      s.startsWith "PowerConvexity.classicalDirichlet_power_" ||
      s == "PowerConvexity.classicalDirichlet_strictConvexOn_two" ||
      s == "PowerConvexity.constantDensity_power_Hessian_positive_two" ||
      s == "PowerConvexity.power_convexOn_closure_of_boundary_decay_two" ||
      s == "PowerConvexity.minkowski_classicalDirichlet_firstJets_continuousAt_two" ||
      s.startsWith "PowerConvexityComparator.Solution." ||
      s.startsWith "PowerConvexityComparator.Check."
    unless bad.isEmpty do
      throwError "Forbidden old-endpoint/old-comparator dependency in {root}: {bad}"
    logInfo m!"PASS: {root}; {deps.size} public/private project+CHS dependencies; no old endpoint or comparator solution."

end PowerConvexityComparator.OriginalRoute
