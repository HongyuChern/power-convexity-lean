import PowerConvexity.Analysis.ActualFlatDriftResidualContinuityFour
import PowerConvexity.Analysis.ActualFlatDriftFrozenImprovementFour
import PowerConvexity.Analysis.ActualFlatIterationDataFour

/-! # Fixed actual input and quantitative smallness for the drift iteration -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualFlatDriftIterationInputFour (N : E) (lam Lambda alpha kappa : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  drift : E → E
  source : E → ℝ
  solution : E → ℝ
  lower : coeff.lam=lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  continuous : ∀ i j, ContinuousOn (fun x => coeff.a x i j) (actualFlatClosedUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour coeff.a x=drift x
  growth : ∀ x ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ kappa*‖x‖^alpha
  drift_continuous : ContinuousOn drift (actualFlatClosedUpperBallFour N 1)
  drift_bound : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x‖ ≤ kappa
  drift_growth : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x-drift 0‖ ≤ kappa*‖x‖^alpha
  source_continuous : ContinuousOn source (actualFlatClosedUpperBallFour N 1)
  source_growth : ∀ x ∈ actualFlatUpperBallFour N 1, |source x-source 0| ≤ kappa*‖x‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ 1
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j)+fderiv ℝ solution x (drift x) = -source x

theorem actual_flat_drift_residual_small_four {N : E} {lam Lambda alpha kappa R a M G delta : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hk : 0 ≤ kappa)
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a) (hRa : R^alpha ≤ a)
    (hM : 0 ≤ M) (hG : 0 ≤ G) (hsmall : kappa*(1+17*M+G) ≤ delta)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) (hH : ‖realHessian q 0‖ ≤ M)
    (hD : ‖fderiv ℝ q 0‖ ≤ G)
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 (D.drift 0) = -D.source 0) :
    ∀ z ∈ actualFlatUpperBallFour N 1,
      |actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source q R a z| ≤ delta := by
  intro z hz
  have hm := actual_flat_unit_dilation_maps_four N hR hR1 hz
  have hzn : ‖z‖ ≤ 1 := by
    have hh : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact hh.le
  have hxn : ‖R • z‖ ≤ R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hzn hR.le
  have hxp : ‖R • z‖^alpha ≤ a :=
    (Real.rpow_le_rpow (norm_nonneg _) hxn halpha.le).trans hRa
  have hxa : ‖R • z‖ ≤ a :=
    hxn.trans ((Real.self_le_rpow_of_le_one hR.le hR1 halpha1).trans hRa)
  have hbound := actual_full_drift_residual_holder_growth_four D.coeff.a D.drift D.source hq
    hk hk hk hM hG hH hD hfreeze D.growth D.drift_growth D.drift_bound D.source_growth _ hm
  have hc : 0 ≤ kappa+16*kappa*M+G*kappa := by positivity
  have hb : |D.source (R • z)-quadraticScalarSourceTwo D.coeff.a q (R • z)+
      fderiv ℝ q (R • z) (D.drift (R • z))| ≤ a*(kappa*(1+17*M+G)) :=
    hbound.trans ((add_le_add (mul_le_mul_of_nonneg_left hxp hc)
      (mul_le_mul_of_nonneg_left hxa (mul_nonneg hM hk))).trans_eq (by ring))
  simp only [actualFlatDriftResidualSourceFour,abs_mul,abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ a⁻¹*(a*(kappa*(1+17*M+G))) := mul_le_mul_of_nonneg_left hb (inv_pos.mpr ha).le
    _ = kappa*(1+17*M+G) := by rw [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]
    _ ≤ delta := hsmall

end PowerConvexity
