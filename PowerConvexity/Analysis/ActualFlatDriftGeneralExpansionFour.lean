import PowerConvexity.Analysis.ActualFlatDriftSourceNormalizationFour
import PowerConvexity.Analysis.ActualFlatPhysicalExpansionFour

/-! # Actual boundary expansion with unrestricted constant source -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_general_quadratic_expansion_four {lam Lambda alpha F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hF : 0 ≤ F) :
    ∃ C > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa, |D.source 0| ≤ F →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        (realBlockHessian realDirections imagDirections p 0).trace+
          fderiv ℝ p 0 (D.drift 0) = -D.source 0 ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
          |D.solution x-p x| ≤ C*(1/2 : ℝ)^n*(r^n)^2 := by
  obtain ⟨C0,hC0,r,hr,hr8,hrp,hexp⟩ :=
    actual_flat_drift_normalized_quadratic_expansion_four hlam hLambda halpha halpha1
  let a := 1+F
  have ha : 0 < a := by dsimp only [a]; linarith
  have ha1 : 1 ≤ a := by dsimp only [a]; linarith
  let C := 1+F+a*C0
  have hC : 0 < C := by dsimp only [C]; positivity
  have haC : a*C0 ≤ C := by dsimp only [C]; linarith
  have hFaC : F+a*C0 ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,r,hr,hr8,hrp,?_⟩
  intro N hN
  obtain ⟨tau,htau,htau1,hpoly⟩ := hexp N hN
  let kappa := tau/(1+17*F)
  have hk : 0 < kappa := by dsimp only [kappa]; positivity
  have hden : 0 < 1+17*F := by positivity
  have hkEq : kappa*(1+17*F)=tau := div_mul_cancel₀ tau hden.ne'
  have hkt : kappa ≤ tau := by nlinarith [mul_nonneg hk.le hF]
  have hsource : a⁻¹*kappa*(1+17*F) ≤ tau := by
    rw [mul_assoc,hkEq]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ ha).mpr (by nlinarith [mul_le_mul_of_nonneg_left ha1 htau.le])
  have hsize : 1+F/2 ≤ a := by dsimp only [a]; linarith
  refine ⟨kappa,hk,hkt.trans htau1,?_⟩
  intro D hf0
  let D' := actualFlatDriftRemoveSourceFour hN halpha halpha1 hk.le hF ha hkt hsize hsource D hf0
  let q := actualFlatSourceQuadraticFour N (D.source 0)
  have hq := actualFlatSourceQuadraticFour_quadratic N (D.source 0)
  have hq0 : ∀ x : E, inner ℝ N x=0 → q x=0 := fun _ hx => actualFlatSourceQuadraticFour_zero N _ hx
  have hD0 : D'.source 0=0 :=
    actual_flat_drift_residual_source_zero_four (actual_flat_drift_input_frozen_four hN halpha D)
      (actual_flat_source_quadratic_full_frozen_four hN _ _) 1 a
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := hpoly D' hD0
  have hpfreeze : (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 ((1 : ℝ) • D.drift 0) = 0 := by
    rw [hD0,neg_zero] at hpt
    change (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (D.drift 0) = 0 at hpt
    simpa only [one_smul] using hpt
  let P := scalarQuadraticUpdateTwo q p 1 a
  obtain ⟨_,hinc1,hinc2⟩ := scalarQuadraticUpdateTwo_jet_increment_bounds hq hp zero_lt_one ha.le
    (show |p 0| ≤ C0 by rw [hp0 0 (by simp),abs_zero]; exact hC0.le) hpD (hpH 0)
  have hPD : ‖fderiv ℝ P 0‖ ≤ C := by
    change ‖fderiv ℝ P 0-fderiv ℝ q 0‖ ≤ a*1*C0 at hinc1
    rw [actualFlatSourceQuadraticFour_fderiv_zero,sub_zero,mul_one] at hinc1
    exact hinc1.trans haC
  refine ⟨P,scalarQuadraticUpdateTwo_isQuadratic hq hp 1 a,
    actual_flat_quadratic_update_zero_four zero_lt_one hq0 hp0,
    actual_flat_drift_quadratic_update_frozen_four hq hp zero_lt_one _ _
      (actual_flat_source_quadratic_full_frozen_four hN _ _) hpfreeze,hPD,?_,?_⟩
  · intro x
    calc
      ‖realHessian P x‖ ≤ ‖realHessian q x‖+‖realHessian P x-realHessian q x‖ :=
        norm_le_insert' (realHessian P x) (realHessian q x)
      _ ≤ |D.source 0|+a*C0 := add_le_add
        (actualFlatSourceQuadraticFour_hessian_norm hN (D.source 0) x).le (hinc2 x)
      _ ≤ C := (add_le_add hf0 (le_refl (a*C0))).trans hFaC
  · intro n x hx
    have he := actual_flat_physical_residual_error_four (R := 1) zero_lt_one ha (herr n) x
      (by simpa only [one_mul] using hx)
    change |D.solution x-P x| ≤ (a*(C0*(1/2 : ℝ)^n))*(1*r^n)^2 at he
    calc
      _ ≤ (a*C0)*(1/2 : ℝ)^n*(r^n)^2 := he.trans_eq (by ring)
      _ ≤ C*(1/2 : ℝ)^n*(r^n)^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right haC (by positivity)) (sq_nonneg _)

end PowerConvexity
