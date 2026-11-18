import PowerConvexity.Analysis.ActualUniformFlatQuotientDataFour
import PowerConvexity.Analysis.ActualScalarCoefficientNormalizationFour

/-! # Actual ellipticity and amplitude normalization for the quotient equation

Both constructors retain the same coefficient/divergence identity and real
response. Every source and drift factor is explicit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatQuotientNormalizeFour {N : E} {B F : ℝ}
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) (actualFlatUpperBallFour N 1))
    (hpos : ∀ x ∈ actualFlatUpperBallFour N 1, (A.a x).PosDef)
    (b : E → E) (hb : ContinuousOn b (actualFlatUpperBallFour N 1))
    (hdiv : ∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour A.a x=b x)
    (hbb : ∀ x ∈ actualFlatUpperBallFour N 1, ‖b x‖ ≤ B)
    (f u : E → ℝ) (hf : ContinuousOn f (actualFlatUpperBallFour N 1))
    (hfb : ∀ x ∈ actualFlatUpperBallFour N 1, |f x| ≤ F)
    (hu : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (heq : ∀ x ∈ actualFlatUpperBallFour N 1,
      (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x) :
    ActualFlatQuotientEquationFour N (A.Λ/A.lam) (B/A.lam) (F/A.lam) := by
  refine {
    coeff := actualScalarNormalizedCoeffFour A
    upper := le_refl _
    regular := fun i j => contDiffOn_const.mul (hA i j)
    positive := fun x hx => (hpos x hx).smul (inv_pos.mpr A.hlam)
    drift := fun x => A.lam⁻¹ • b x
    drift_continuous := hb.const_smul A.lam⁻¹
    divergence := ?_
    drift_bound := ?_
    source := fun x => A.lam⁻¹*f x
    source_continuous := continuousOn_const.mul hf
    source_bound := ?_
    solution := u
    solution_regular := hu
    solution_continuous := huC
    equation := ?_
  }
  · intro x hx
    rw [actual_scalar_normalized_column_divergence_four A
      (fun i j => ((hA i j).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds hx)).differentiableAt
        (by norm_num)),hdiv x hx]
  · intro x hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr A.hlam)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left (hbb x hx) (inv_nonneg.mpr A.hlam.le)
  · intro x hx
    rw [abs_mul,abs_of_pos (inv_pos.mpr A.hlam)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left (hfb x hx) (inv_nonneg.mpr A.hlam.le)
  · intro x hx
    change (∑ i, ∑ j, (A.lam⁻¹*A.a x i j)*euclideanHessian u x i j)+
      fderiv ℝ u x (A.lam⁻¹ • b x) = -(A.lam⁻¹*f x)
    simp only [map_smul,smul_eq_mul]
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [← mul_add,heq x hx,mul_neg]

def actualFlatQuotientAmplitudeFour {N : E} {Lambda B F c : ℝ}
    (hc : 0 ≤ c) (D : ActualFlatQuotientEquationFour N Lambda B F) :
    ActualFlatQuotientEquationFour N Lambda B (c*F) := by
  refine {
    coeff := D.coeff
    upper := D.upper
    regular := D.regular
    positive := D.positive
    drift := D.drift
    drift_continuous := D.drift_continuous
    divergence := D.divergence
    drift_bound := D.drift_bound
    source := fun x => c*D.source x
    source_continuous := continuousOn_const.mul D.source_continuous
    source_bound := ?_
    solution := fun x => c*D.solution x
    solution_regular := contDiffOn_const.mul D.solution_regular
    solution_continuous := continuousOn_const.mul D.solution_continuous
    equation := ?_
  }
  · intro x hx
    rw [abs_mul,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (D.source_bound x hx) hc
  · intro x hx
    simpa only [zero_mul,add_zero,sub_zero] using
      actual_normal_affine_response_equation_four N c 0 (D.coeff.1.a x) (D.drift x)
        (D.solution_regular.contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds hx)) (D.equation x hx)

def actualFlatQuotientIncreaseBoundsFour {N : E} {Lambda B F B' F' : ℝ}
    (hB : B ≤ B') (hF : F ≤ F') (D : ActualFlatQuotientEquationFour N Lambda B F) :
    ActualFlatQuotientEquationFour N Lambda B' F' where
  coeff := D.coeff
  upper := D.upper
  regular := D.regular
  positive := D.positive
  drift := D.drift
  drift_continuous := D.drift_continuous
  divergence := D.divergence
  drift_bound := fun x hx => (D.drift_bound x hx).trans hB
  source := D.source
  source_continuous := D.source_continuous
  source_bound := fun x hx => (D.source_bound x hx).trans hF
  solution := D.solution
  solution_regular := D.solution_regular
  solution_continuous := D.solution_continuous
  equation := D.equation

end PowerConvexity
