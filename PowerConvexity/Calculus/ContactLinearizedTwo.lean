import PowerConvexity.Calculus.CriticalContactTwo

/-! # The actual elliptic operator at a simple zero contact -/
set_option autoImplicit false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem modifiedSigmaTwo_critical_zero_linearized_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hzero : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) :
    complexLinearized a b u (modifiedSigmaTwo a b u) x ≤ 0 :=
  modifiedSigmaTwo_critical_zero_contraction_nonpos hU hu a b hρ hdet hneg hA hx hzero hgap hc

theorem modifiedSigmaTwo_localMin_zero_linearized_eq_zero {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hzero : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hm : IsLocalMin (modifiedSigmaTwo a b u) x) :
    complexLinearized a b u (modifiedSigmaTwo a b u) x = 0 := by
  apply le_antisymm
  · exact modifiedSigmaTwo_critical_zero_linearized_nonpos hU hu a b hρ hdet hneg hA hx hzero hgap hm.fderiv_eq_zero
  · have hs := modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) a b (hA x hx) hgap
    rw [complexLinearized_eq_real a b u hs]
    apply complexHessianContraction_positive a b (hA x hx).inv
    exact realHessian_nonneg_of_isLocalMin hs hm

end PowerConvexity
