import PowerConvexity.Analysis.ActualFrozenCoefficientNormalizationTwo
import PowerConvexity.Analysis.ActualLinearEllipticPullbackTwo
import PowerConvexity.Analysis.ActualCofactorQuadraticResidualTwo

/-! A checked call joining the constructed normalization to actual weak transport.
The next lemma can use the same coordinates for the coefficient's regularity
and column divergence. -/

open Set MeasureTheory
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem c112_resume_normalized_actual_weak_transport {U : Set E}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) (x₀ : E) (hA : (A.a x₀).PosDef)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E,
      (actualLinearPullbackCoeffTwo G A).a (G.symm x₀) = 1 ∧
      ActualScalarWeakEquationTwo (actualLinearPullbackCoeffTwo G A)
        (fun z => f (G z)) (fun z => u (G z)) := by
  obtain ⟨G, hG⟩ := actual_positive_frozen_normalization_two hA
  refine ⟨G, ?_, actual_scalar_weak_constructed_linear_pullback_two hU hUb G A hf hu⟩
  change actualLinearCongruenceMatrixTwo G (A.a (G (G.symm x₀))) = 1
  simpa only [G.apply_symm_apply] using hG

end PowerConvexity
