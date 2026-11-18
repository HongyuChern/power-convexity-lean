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

end PowerConvexityComparator.OriginalRoute
