import PowerConvexity.Analysis.ActualFlatCorrectedSourceBoundsFour
import PowerConvexity.Analysis.ActualFlatNormalizedExpansionFour

/-! # Actual physical normalization at a flat boundary point
The coefficient at zero remains I, and the normal quadratic removes the
actual source value without changing the flat zero boundary data.
-/
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

structure ActualFlatLinearInputFour (N : E) (lam Lambda alpha Ka Kf B : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  frozen : coeff.a 0=1
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤ Ka*‖x-y‖^alpha
  growth : ∀ x ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha
  source_regular : ContDiffOn ℝ 1 source (actualFlatUpperBallFour N 1)
  source_holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    |source x-source y| ≤ Kf*‖x-y‖^alpha
  source_growth : ∀ x ∈ actualFlatUpperBallFour N 1, |source x-source 0| ≤ Kf*‖x‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ B
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

theorem actual_flat_normalization_parameters_four {Ka Kf B F alpha kappa : ℝ}
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (halpha : 0 < alpha) (hkappa : 0 < kappa) :
    ∃ R > 0, R ≤ 1 ∧ ∃ a > 0,
      Ka*R^alpha ≤ kappa ∧ a⁻¹*R^alpha*(Kf+16*Ka*F) ≤ kappa ∧ B+F/2 ≤ a*R^2 := by
  let R := min 1 ((kappa/(Ka+1))^alpha⁻¹)
  have hKa1 : 0 < Ka+1 := by linarith
  have hR : 0 < R := lt_min zero_lt_one (Real.rpow_pos_of_pos (div_pos hkappa hKa1) _)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRp : R^alpha ≤ kappa/(Ka+1) := by
    apply (Real.rpow_le_rpow hR.le (min_le_right _ _) halpha.le).trans_eq
    exact Real.rpow_inv_rpow (div_pos hkappa hKa1).le halpha.ne'
  have hRpK : R^alpha ≤ kappa := hRp.trans (by
    apply (div_le_iff₀ hKa1).mpr
    nlinarith [mul_nonneg hkappa.le hKa])
  have hcoeff : Ka*R^alpha ≤ kappa := by
    have hh := (le_div_iff₀ hKa1).mp hRp
    nlinarith [Real.rpow_nonneg hR.le alpha]
  let S := B+F+Kf+16*Ka*F+1
  have hS : 0 < S := by dsimp only [S]; positivity
  have hK : Kf+16*Ka*F ≤ S := by dsimp only [S]; linarith
  have hBF : B+F/2 ≤ S := by dsimp only [S]; nlinarith [mul_nonneg hKa hF]
  let a := S/R^2
  have ha : 0 < a := div_pos hS (sq_pos_of_pos hR)
  have hR2 : R^2 ≤ 1 := by nlinarith [hR.le,hR1]
  have hSa : S ≤ a := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    exact (mul_le_mul_of_nonneg_left hR2 hS.le).trans_eq (mul_one S)
  have hfac : a⁻¹*(Kf+16*Ka*F) ≤ 1 := by
    rw [inv_mul_eq_div]
    exact (div_le_one ha).mpr (hK.trans hSa)
  refine ⟨R,hR,hR1,a,ha,hcoeff,?_,?_⟩
  · calc
      a⁻¹*R^alpha*(Kf+16*Ka*F) = (a⁻¹*(Kf+16*Ka*F))*R^alpha := by ring
      _ ≤ 1*R^alpha := mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hR.le alpha)
      _ ≤ kappa := by simpa only [one_mul] using hRpK
  · simpa only [a,div_mul_cancel₀ _ (sq_pos_of_pos hR).ne'] using hBF

def actualFlatNormalizeFour {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha Ka Kf B kappa R a : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a)
    (D : ActualFlatLinearInputFour N lam Lambda alpha Ka Kf B)
    (hcoeff : Ka*R^alpha ≤ kappa)
    (hsource : a⁻¹*R^alpha*(Kf+16*Ka*|D.source 0|) ≤ kappa)
    (hsize : B+|D.source 0|/2 ≤ a*R^2) :
    ActualFlatIterationInputFour N lam Lambda alpha kappa := by
  let q := actualFlatSourceQuadraticFour N (D.source 0)
  have hq := actualFlatSourceQuadraticFour_quadratic N (D.source 0)
  have hq0 (x : E) (hx : inner ℝ N x=0) : q x=0 := actualFlatSourceQuadraticFour_zero N _ hx
  have hreg := actual_flat_residual_regularity_four (b := a) hR hR1 hq D.solution_regular
    D.solution_continuous D.solution_zero hq0
  have herr : ∀ x ∈ actualFlatClosedUpperBallFour N R, |D.solution x-q x| ≤ a*R^2 := by
    intro x hx
    have hx1 : x ∈ actualFlatClosedUpperBallFour N 1 :=
      ⟨closedBall_subset_closedBall hR1 hx.1,hx.2⟩
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx1.1
    have hsq : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hqb : |q x| ≤ |D.source 0|/2 :=
      (actualFlatSourceQuadraticFour_value_bound hN (D.source 0) x).trans
        ((mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ |D.source 0|/2)).trans_eq (mul_one _))
    exact (abs_sub _ _).trans ((add_le_add (D.solution_bound x hx1) hqb).trans hsize)
  exact {
    coeff := actualFlatDilationCoeffFour hR hR1 D.coeff
    source := actualFlatResidualSourceFour D.coeff.a D.source q R a
    solution := normalizedScalarResidualTwo D.solution q R a
    lower := D.lower
    upper := D.upper
    positive := fun x hx => D.positive _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
    regular := actual_flat_dilation_coeff_regular_four hR hR1 D.coeff D.regular
    divergence := actual_flat_dilation_coeff_divergence_four hR hR1 D.coeff D.regular D.divergence
    holder := by
      intro x hx y hy
      exact (actual_flat_dilation_operator_holder_four hR hR1 D.holder x hx y hy).trans
        (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg _) alpha))
    growth := by
      intro x hx
      have hh := D.growth _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
      have he : Ka*‖R • x‖^alpha = (Ka*R^alpha)*‖x‖^alpha := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
        ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg x) alpha))
    source_regular := actual_flat_residual_source_regular_four hR hR1 D.regular D.source_regular hq
    source_holder := by
      intro x hx y hy
      exact (actual_flat_scaled_corrected_source_holder_four hN hR hR1 ha D.holder
        D.source_holder x hx y hy).trans
        (mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg (norm_nonneg _) alpha))
    source_growth := by
      intro x hx
      exact (actual_flat_scaled_corrected_source_growth_four hN hR hR1 ha D.growth
        D.source_growth x hx).trans
        (mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg (norm_nonneg _) alpha))
    solution_regular := hreg.1
    solution_continuous := hreg.2.1
    solution_zero := hreg.2.2
    solution_bound := actual_flat_residual_bound_four hR ha herr
    equation := fun x hx => actual_normalized_residual_equation_four
      (actualFlatUpperBallFour_isOpen N 1) hR D.solution_regular hq D.equation x
      (actual_flat_unit_dilation_maps_four N hR hR1 hx)
  }

theorem actual_flat_normalization_frozen_identity_four {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha Ka Kf B kappa R a : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a)
    (D : ActualFlatLinearInputFour N lam Lambda alpha Ka Kf B)
    (hcoeff : Ka*R^alpha ≤ kappa)
    (hsource : a⁻¹*R^alpha*(Kf+16*Ka*|D.source 0|) ≤ kappa)
    (hsize : B+|D.source 0|/2 ≤ a*R^2) :
    (actualFlatNormalizeFour hN hR hR1 ha D hcoeff hsource hsize).coeff.a 0=1 :=
  actual_flat_dilation_frozen_identity_four hR hR1 D.coeff D.frozen

end PowerConvexity
