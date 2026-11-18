import PowerConvexity.Analysis.ActualFlatResidualHolderFour
import PowerConvexity.Analysis.ActualFlatQuadraticImprovementFour

/-! # One fixed actual PDE supplies every flat-boundary residual datum -/
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

structure ActualFlatIterationInputFour (N : E) (lam Lambda alpha kappa : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤
      kappa*‖x-y‖^alpha
  growth : ∀ x ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤
      kappa*‖x‖^alpha
  source_regular : ContDiffOn ℝ 1 source (actualFlatUpperBallFour N 1)
  source_holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    |source x-source y| ≤ kappa*‖x-y‖^alpha
  source_growth : ∀ x ∈ actualFlatUpperBallFour N 1, |source x| ≤ kappa*‖x‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ 1
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

structure ActualFlatQuadraticStateFour (N : E) (u : E → ℝ) (R b M : ℝ) where
  polynomial : E → ℝ
  quadratic : IsQuadraticPolynomial polynomial
  zero : ∀ x : E, inner ℝ N x=0 → polynomial x=0
  trace : ∀ x, (realBlockHessian realDirections imagDirections polynomial x).trace=0
  hessian : ‖realHessian polynomial 0‖ ≤ 2*M*(1-b)
  error : ∀ x ∈ actualFlatClosedUpperBallFour N R, |u x-polynomial x| ≤ b*R^2

theorem actual_flat_norm_rpow_le_one_four {N x : E} {alpha : ℝ}
    (halpha : 0 ≤ alpha) (hx : x ∈ actualFlatUpperBallFour N 1) : ‖x‖^alpha ≤ 1 := by
  have hx1 : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx.1
  exact Real.rpow_le_one (norm_nonneg x) hx1.le halpha

def actualFlatResidualDataFour {N : E} {lam Lambda alpha kappa R b M delta : ℝ}
    (halpha : 0 < alpha) (hkappa : 0 ≤ kappa) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 ≤ M) (hRa : R^alpha ≤ b)
    (hsmall : kappa*(1+16*M) ≤ delta) (hd1 : delta ≤ 1)
    (D : ActualFlatIterationInputFour N lam Lambda alpha kappa)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0)
    (hqt : ∀ x, (realBlockHessian realDirections imagDirections q x).trace=0)
    (hqH : ‖realHessian q 0‖ ≤ M)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R, |D.solution x-q x| ≤ b*R^2) :
    ActualFlatPerturbationDataFour N lam Lambda 1 1 alpha delta := by
  have hkdelta : kappa ≤ delta :=
    (show kappa ≤ kappa*(1+16*M) by nlinarith [mul_nonneg hkappa hM]).trans hsmall
  have hpower : R^alpha ≤ 1 := hRa.trans hb1
  have hcoeff : kappa*R^alpha ≤ delta :=
    (mul_le_mul_of_nonneg_left hpower hkappa).trans (by simpa only [mul_one] using hkdelta)
  have hfac : b⁻¹*R^alpha ≤ 1 := by
    rw [inv_mul_eq_div]
    exact (div_le_one hb).mpr hRa
  let S := b⁻¹*R^alpha*(kappa+16*kappa*M)
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hS : S ≤ delta := by
    calc
      S = (b⁻¹*R^alpha)*(kappa*(1+16*M)) := by dsimp only [S]; ring
      _ ≤ 1*delta := mul_le_mul hfac hsmall (by positivity) (by norm_num)
      _ = delta := one_mul _
  have hreg := actual_flat_residual_regularity_four (b := b) hR hR1 hq D.solution_regular
    D.solution_continuous D.solution_zero hq0
  exact {
    coeff := actualFlatDilationCoeffFour hR hR1 D.coeff
    source := actualFlatResidualSourceFour D.coeff.a D.source q R b
    solution := normalizedScalarResidualTwo D.solution q R b
    lower := D.lower
    upper := D.upper
    positive := fun x hx => D.positive _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
    regular := actual_flat_dilation_coeff_regular_four hR hR1 D.coeff D.regular
    divergence := actual_flat_dilation_coeff_divergence_four hR hR1 D.coeff D.regular D.divergence
    holder := by
      intro x hx y hy
      exact (actual_flat_dilation_operator_holder_four hR hR1 D.holder x hx y hy).trans
        (mul_le_mul_of_nonneg_right (hcoeff.trans hd1) (Real.rpow_nonneg (norm_nonneg _) alpha))
    near_identity := by
      intro x hx i j
      have hm := actual_flat_unit_dilation_maps_four N hR hR1 hx
      have hh := (actual_matrix_difference_entry_bound_four (D.coeff.a (R • x)) 1 i j).trans
        (D.growth _ hm)
      have he : kappa*‖R • x‖^alpha = (kappa*R^alpha)*‖x‖^alpha := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
        ring
      rw [he] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_left (actual_flat_norm_rpow_le_one_four halpha.le hx)
        (mul_nonneg hkappa (Real.rpow_nonneg hR.le alpha))).trans (by simpa using hcoeff))
    source_regular := actual_flat_residual_source_regular_four hR hR1 D.regular D.source_regular hq
    source_holder := by
      intro x hx y hy
      exact (actual_flat_residual_source_holder_four hq hR hR1 hb hM hqH D.holder
        D.source_holder x hx y hy).trans
        (mul_le_mul_of_nonneg_right (hS.trans hd1) (Real.rpow_nonneg (norm_nonneg _) alpha))
    source_bound := by
      intro x hx
      exact (actual_flat_residual_source_growth_four hq hR hR1 hb hkappa hM hqH hqt
        D.growth D.source_growth x hx).trans
        ((mul_le_mul_of_nonneg_left (actual_flat_norm_rpow_le_one_four halpha.le hx) hS0).trans
          (by simpa only [mul_one] using hS))
    solution_regular := hreg.1
    solution_continuous := hreg.2.1
    solution_zero := hreg.2.2
    solution_bound := actual_flat_residual_bound_four hR hb herr
    equation := fun x hx => actual_normalized_residual_equation_four
      (actualFlatUpperBallFour_isOpen N 1) hR D.solution_regular hq D.equation x
      (actual_flat_unit_dilation_maps_four N hR hR1 hx)
  }

end PowerConvexity
