import PowerConvexity.Targets.StandardComplexTwoFrame

/-! # Literal dimension-two target data and their currently proved consequences

The first two consequences are non-strict. The strict consequence retains an
explicit spectral-gap hypothesis on the zero locus. No unconditional strict
paper endpoint is declared in this module.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

variable {U : Set (EuclideanSpace ℂ (Fin 2))}
  (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hstrict : StrictConvex ℝ U)
  (hsmooth : ∀ x ∈ frontier U, ∃ f : EuclideanSpace ℂ (Fin 2) → ℝ,
    ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
    (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
  {u : EuclideanSpace ℂ (Fin 2) → ℝ}
  (hu4 : ContDiffOn ℝ 4 u U) (hJ : Nonempty (ClosureC2Jet u U))
  (hboundary : ∀ x ∈ frontier U, u x = 0)
  (hpsh : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) u x).PosDef)
  (hdet : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) u x).det = 1)

include hU hbounded hstrict hsmooth hu4 hJ hboundary hpsh hdet

theorem mainTwo_target_nonstrict_chord :
    ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) ≤
        a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) := by
  obtain ⟨J⟩ := hJ
  have hc := classicalDirichlet_power_convexOn_closure_two hU hstrict.convex
    hbounded.isCompact_closure (smoothLocalDefiningFunction_implies_C2 hsmooth)
    J.continuous_value (hu4.of_le (by norm_num)) hboundary
    standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j)
    standardComplexTwoBasis_real_orthonormal hpsh hdet
  intro x hx y hy a b ha hb hab
  exact hc.2 hx hy ha hb hab

theorem mainTwo_target_nonnegative_realHessian :
    ∀ x ∈ U, ∀ v : EuclideanSpace ℂ (Fin 2),
      0 ≤ fderiv ℝ (fderiv ℝ (fun y => -Real.sqrt (-u y))) x v v := by
  obtain ⟨J⟩ := hJ
  have hu2 : ContDiffOn ℝ 2 u U := hu4.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hbounded.isCompact_closure
    J.continuous_value hu2 hboundary standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) hpsh
  have hc := classicalDirichlet_power_convexOn_two hU hstrict.convex
    hbounded.isCompact_closure (smoothLocalDefiningFunction_implies_C2 hsmooth)
    J.continuous_value hu2 hboundary standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j)
    standardComplexTwoBasis_real_orthonormal hpsh hdet
  intro x hx v
  exact realHessian_nonneg_of_convexOn hU (powerTransform_contDiffOn hu2 hneg) hc hx v

theorem mainTwo_target_strict_chord_of_zero_locus_gap
    (hgap : ∀ x ∈ U, modifiedSigmaTwo standardComplexTwoBasis
        (fun j => Complex.I • standardComplexTwoBasis j) u x = 0 →
      0 < eigenDiscriminantTwo (modifiedK standardComplexTwoBasis
        (fun j => Complex.I • standardComplexTwoBasis j) u x)) :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ∀ a b : ℝ,
      0 < a → 0 < b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) <
        a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) := by
  obtain ⟨J⟩ := hJ
  have hc := classicalDirichlet_strictConvexOn_of_zero_locus_gap_two
    standardComplexTwoBasis standardComplexTwoBasis_real_orthonormal hU hstrict.convex
    hbounded.isCompact_closure (smoothLocalDefiningFunction_implies_C2 hsmooth)
    J.continuous_value hu4 hboundary hpsh hdet hgap
  intro x hx y hy hxy a b ha hb hab
  exact hc.2 hx hy hxy ha hb hab

end PowerConvexity
