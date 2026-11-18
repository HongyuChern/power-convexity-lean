import PowerConvexity.Calculus.ActualUncenteredOriginalPowerConvexityTwo
import PowerConvexity.Analysis.StrictBoundaryChords
import PowerConvexity.Targets.StandardComplexTwoFrame

/-! # Frozen main-theorem statement through the newly completed original route

The hypotheses and conclusion match the accepted paper endpoint. The proof
uses the actual existence/common-collar/approximation route, not the old
power-convexity endpoint. Smoothness is retained in this exact paper-facing
interface even though the newly proved original-domain result needs less.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem actual_original_route_mainTheorem
    {U : Set (EuclideanSpace ℂ (Fin 2))}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hchords : HasStrictBoundaryChords U)
    (_hsmooth : ∀ x ∈ frontier U, ∃ f : EuclideanSpace ℂ (Fin 2) → ℝ,
      ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
    {u : EuclideanSpace ℂ (Fin 2) → ℝ}
    (hu4 : ContDiffOn ℝ 4 u U) (hJ : Nonempty (ClosureC2Jet u U))
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (hpsh : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
      (fun j => Complex.I • standardComplexTwoBasis j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
      (fun j => Complex.I • standardComplexTwoBasis j) u x).det = 1) :
    StrictConvexOn ℝ U (fun x => -Real.sqrt (-u x)) := by
  exact (actual_original_dirichlet_hessian_sigma_strictConvex_uncentered_two
    hU (strictBoundaryChords_convex hU hchords) hbounded.isCompact_closure
    standardComplexTwoBasis standardComplexTwoBasis_real_orthonormal
    ⟨hu4,hJ,hpsh,hdet,hboundary⟩).2.2

end PowerConvexity
