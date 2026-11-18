import PowerConvexity.Calculus.ClassicalStrictConvexityTwo
import PowerConvexity.Targets.GeometricTargetContracts

/-! # The dimension-two endpoint of frozen arXiv:2607.06895v1

This is the original positive branch, actual determinant-one equation and
actual StrictConvexOn conclusion. No spectral gap or analytic estimate is
an additional premise. Closure C2 is represented by the existing actual jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

variable {U : Set (EuclideanSpace ℂ (Fin 2))}
  (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hchords : HasStrictBoundaryChords U)
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
include hU hbounded hchords hsmooth hu4 hJ hboundary hpsh hdet

/-- Frozen TeX mainTheorem, with the strict plurisubharmonic solution branch
made explicit as in the equation's surrounding text. -/
theorem mainTheorem : StrictConvexOn ℝ U (fun x => -Real.sqrt (-u x)) := by
  obtain ⟨J⟩ := hJ
  exact classicalDirichlet_strictConvexOn_two standardComplexTwoBasis
    standardComplexTwoBasis_real_orthonormal hU (strictBoundaryChords_convex hU hchords)
    hbounded.isCompact_closure (smoothLocalDefiningFunction_implies_C2 hsmooth)
    J.continuous_value hu4 hboundary hpsh hdet

theorem mainTwo_geometric_target_strict_chord :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ∀ a b : ℝ,
      0 < a → 0 < b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) <
        a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) := by
  have hc := mainTheorem hU hbounded hchords hsmooth hu4 hJ hboundary hpsh hdet
  intro x hx y hy hxy a b ha hb hab
  exact hc.2 hx hy hxy ha hb hab

theorem mainTwo_geometric_target_positive_realHessian :
    ∀ x ∈ U, ∀ v : EuclideanSpace ℂ (Fin 2), v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun y => -Real.sqrt (-u y))) x v v := by
  obtain ⟨J⟩ := hJ
  have hc := classicalDirichlet_power_convexOn_two hU (strictBoundaryChords_convex hU hchords)
    hbounded.isCompact_closure (smoothLocalDefiningFunction_implies_C2 hsmooth)
    J.continuous_value (hu4.of_le (by norm_num)) hboundary
    standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j)
    standardComplexTwoBasis_real_orthonormal hpsh hdet
  exact constantDensity_power_Hessian_positive_two standardComplexTwoBasis hU
    hbounded.isCompact_closure J.continuous_value hu4 hboundary hpsh
    (by norm_num : (1:ℂ) ≠ 0) hdet hc

end PowerConvexity
