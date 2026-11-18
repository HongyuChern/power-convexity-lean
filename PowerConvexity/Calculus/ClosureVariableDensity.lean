import PowerConvexity.Calculus.ClosureStrictBranch

/-! # Actual variable determinant data extend to the closure jet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem closure_complexField_variableDensity {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) {ρ : E → ℂ} (hρ : ContinuousOn ρ (closure U))
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = ρ x) :
    ∀ x ∈ closure U, (J.complexField a b x).det = ρ x := by
  have he : EqOn (fun x => (J.complexField a b x).det) ρ U := by
    intro x hx
    change (J.complexField a b x).det = ρ x
    rw [closure_complexField_eq_interior J hx (hu.contDiffAt (hU.mem_nhds hx)) a b]
    exact hdet x hx
  exact he.of_subset_closure
    (continuous_id.matrix_det.comp_continuousOn (J.continuousOn_complexField a b))
    hρ subset_closure Subset.rfl

theorem closure_complexField_posDef_of_variableDensity {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) {ρ : E → ℂ} (hρ : ContinuousOn ρ (closure U))
    (hρ0 : ∀ x ∈ closure U, ρ x ≠ 0)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = ρ x)
    (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef) :
    ∀ x ∈ closure U, (J.complexField a b x).PosDef := by
  intro x hx
  apply (closure_complexField_posSemidef J hU hu a b
    (fun y hy => (hpos y hy).posSemidef) x hx).posDef_iff_det_ne_zero.mpr
  rw [closure_complexField_variableDensity J hU hu a b hρ hdet x hx]
  exact hρ0 x hx

end PowerConvexity
