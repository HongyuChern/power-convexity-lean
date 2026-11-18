import PowerConvexity.Analysis.ActualFlatDriftGeneralExpansionFour

/-! # Actual physical input and a simultaneous admissible physical scale -/
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

structure ActualFlatDriftPhysicalInputFour (N : E) (lam Lambda alpha Ka Kb Kf Bd B : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  drift : E → E
  source : E → ℝ
  solution : E → ℝ
  lower : coeff.lam=lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  frozen : coeff.a 0=1
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  continuous : ∀ i j, ContinuousOn (fun x => coeff.a x i j) (actualFlatClosedUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour coeff.a x=drift x
  growth : ∀ x ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha
  drift_continuous : ContinuousOn drift (actualFlatClosedUpperBallFour N 1)
  drift_bound : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x‖ ≤ Bd
  drift_growth : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x-drift 0‖ ≤ Kb*‖x‖^alpha
  source_continuous : ContinuousOn source (actualFlatClosedUpperBallFour N 1)
  source_growth : ∀ x ∈ actualFlatUpperBallFour N 1, |source x-source 0| ≤ Kf*‖x‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ B
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j)+fderiv ℝ solution x (drift x) = -source x

theorem actual_flat_drift_physical_scale_four {alpha Ka Kb Kf Bd B F kappa : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKf : 0 ≤ Kf) (hBd : 0 ≤ Bd)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hk : 0 < kappa) :
    ∃ R > 0, R ≤ 1 ∧ ∃ a > 0, 1 ≤ a ∧ F ≤ a ∧ B ≤ a*R^2 ∧
      Ka*R^alpha ≤ kappa ∧ Kb*R^alpha ≤ kappa ∧ R*Bd ≤ kappa ∧
      a⁻¹*Kf*R^alpha ≤ kappa := by
  let L := Ka+Kb+Kf+Bd+1
  have hL : 0 < L := by dsimp only [L]; positivity
  let R := min 1 ((kappa/L)^alpha⁻¹)
  have hR : 0 < R := lt_min zero_lt_one (Real.rpow_pos_of_pos (div_pos hk hL) _)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRp : R^alpha ≤ kappa/L := by
    apply (Real.rpow_le_rpow hR.le (min_le_right _ _) halpha.le).trans_eq
    exact Real.rpow_inv_rpow (div_pos hk hL).le halpha.ne'
  have hLp : L*R^alpha ≤ kappa := by
    have hh := (le_div_iff₀ hL).mp hRp
    nlinarith
  have hpow : 0 ≤ R^alpha := Real.rpow_nonneg hR.le alpha
  have hfactor : ∀ c : ℝ, c ≤ L → c*R^alpha ≤ kappa :=
    fun c hc => (mul_le_mul_of_nonneg_right hc hpow).trans hLp
  have hca := hfactor Ka (by dsimp only [L]; linarith)
  have hcb := hfactor Kb (by dsimp only [L]; linarith)
  have hcf := hfactor Kf (by dsimp only [L]; linarith)
  have hcd := hfactor Bd (by dsimp only [L]; linarith)
  let a := (B+F+1)/R^2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hR2 : R^2 ≤ 1 := by nlinarith
  have haBig : B+F+1 ≤ a := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    exact (mul_le_mul_of_nonneg_left hR2 (by positivity)).trans_eq (mul_one _)
  have ha1 : 1 ≤ a := by linarith
  have haF : F ≤ a := by linarith
  have hsize : B ≤ a*R^2 := by
    dsimp only [a]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hR).ne']
    linarith
  have hBdR : R*Bd ≤ kappa := by
    have hh := mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_le_one hR.le hR1 halpha1) hBd
    exact hh.trans (by simpa only [mul_comm] using hcd)
  have hsource : a⁻¹*Kf*R^alpha ≤ kappa := by
    calc
      _ = (Kf*R^alpha)/a := by ring
      _ ≤ kappa := (div_le_iff₀ ha).mpr (hcf.trans (by nlinarith [mul_le_mul_of_nonneg_left ha1 hk.le]))
  exact ⟨R,hR,hR1,a,ha,ha1,haF,hsize,hca,hcb,hBdR,hsource⟩

end PowerConvexity
