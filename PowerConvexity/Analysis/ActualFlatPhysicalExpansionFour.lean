import PowerConvexity.Analysis.ActualFlatPhysicalNormalizationFour
import PowerConvexity.Analysis.ActualFlatFrozenEquationFour

/-! # Actual physical quadratic expansion at a flat boundary point
No boundary derivative of the solution is part of the hypotheses.
All constants precede the actual coefficient, source and solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_physical_residual_error_four {N : E} {u q p : E → ℝ}
    {R a s K : ℝ} (hR : 0 < R) (ha : 0 < a)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N s,
      |normalizedScalarResidualTwo u q R a x-p x| ≤ K*s^2) :
    ∀ x ∈ actualFlatClosedUpperBallFour N (R*s),
      |u x-scalarQuadraticUpdateTwo q p R a x| ≤ (a*K)*(R*s)^2 := by
  intro x hx
  have hm : R⁻¹ • x ∈ actualFlatClosedUpperBallFour N s := by
    have hh := actual_flat_smul_closedUpperBall_four (inv_pos.mpr hR) hx
    simpa only [← mul_assoc,inv_mul_cancel₀ hR.ne',one_mul] using hh
  have he : u x-scalarQuadraticUpdateTwo q p R a x =
      (a*R^2)*(normalizedScalarResidualTwo u q R a (R⁻¹ • x)-p (R⁻¹ • x)) := by
    simp only [scalarQuadraticUpdateTwo,scalarQuadraticLiftTwo_apply hR.ne',
      normalizedScalarResidualTwo,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos (mul_pos ha (sq_pos_of_pos hR))]
  exact (mul_le_mul_of_nonneg_left (herr _ hm) (by positivity : 0 ≤ a*R^2)).trans_eq (by ring)

theorem actual_flat_physical_quadratic_expansion_four {lam Lambda alpha Ka Kf B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧ ∃ C > 0,
      ∀ D : ActualFlatLinearInputFour N lam Lambda alpha Ka Kf B, |D.source 0| ≤ F →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = -D.source 0) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (R*r^n),
          |D.solution x-p x| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2 := by
  obtain ⟨K,hK,r,hr,hr8,hrp,hexp⟩ :=
    actual_flat_normalized_quadratic_expansion_four hlam hLambda halpha
  refine ⟨r,hr,hr8,hrp,?_⟩
  intro N hN
  obtain ⟨kappa,hk,hk1,hp⟩ := hexp N hN
  obtain ⟨R,hR,hR1,a,ha,hcoeff,hsource,hsize⟩ :=
    actual_flat_normalization_parameters_four hKa hKf hB hF halpha hk
  let C := 1+F+a*K+a*R*K
  have hC : 0 < C := by dsimp only [C]; positivity
  have haK : a*K ≤ C := by dsimp only [C]; nlinarith [mul_nonneg (mul_nonneg ha.le hR.le) hK.le]
  have haRK : a*R*K ≤ C := by dsimp only [C]; nlinarith [mul_nonneg ha.le hK.le]
  have hFaK : F+a*K ≤ C := by dsimp only [C]; nlinarith [mul_nonneg (mul_nonneg ha.le hR.le) hK.le]
  refine ⟨R,hR,hR1,C,hC,?_⟩
  intro D hF0
  have hs : a⁻¹*R^alpha*(Kf+16*Ka*|D.source 0|) ≤ kappa := by
    apply le_trans _ hsource
    gcongr
  have hb : B+|D.source 0|/2 ≤ a*R^2 := by linarith
  let D' := actualFlatNormalizeFour hN hR hR1 ha D hcoeff hs hb
  obtain ⟨p,hpq,hp0,hpt,hpD,hpH,herr⟩ := hp D'
  let q := actualFlatSourceQuadraticFour N (D.source 0)
  have hq := actualFlatSourceQuadraticFour_quadratic N (D.source 0)
  let P := scalarQuadraticUpdateTwo q p R a
  have hP := scalarQuadraticUpdateTwo_isQuadratic hq hpq R a
  have hP0 : ∀ x : E, inner ℝ N x=0 → P x=0 :=
    actual_flat_quadratic_update_zero_four hR
      (fun x hx => actualFlatSourceQuadraticFour_zero N _ hx) hp0
  obtain ⟨hinc0,hinc1,hinc2⟩ := scalarQuadraticUpdateTwo_jet_increment_bounds hq hpq hR ha.le
    (show |p 0| ≤ K by rw [hp0 0 (by simp),abs_zero]; exact hK.le) hpD (hpH 0)
  have hD : ‖fderiv ℝ P 0‖ ≤ C := by
    change ‖fderiv ℝ P 0-fderiv ℝ q 0‖ ≤ a*R*K at hinc1
    rw [actualFlatSourceQuadraticFour_fderiv_zero,sub_zero] at hinc1
    exact hinc1.trans haRK
  refine ⟨P,hP,hP0,hD,?_,actual_flat_corrected_quadratic_frozen_trace_four hN hpq hR hpt,?_⟩
  · intro x
    calc
      ‖realHessian P x‖ ≤ ‖realHessian q x‖+‖realHessian P x-realHessian q x‖ :=
        norm_le_insert' (realHessian P x) (realHessian q x)
      _ ≤ |D.source 0|+a*K := add_le_add
        (actualFlatSourceQuadraticFour_hessian_norm hN (D.source 0) x).le (hinc2 x)
      _ ≤ C := (add_le_add hF0 (le_refl (a*K))).trans hFaK
  · intro n x hx
    have he := actual_flat_physical_residual_error_four hR ha (herr n) x hx
    change |D.solution x-P x| ≤ (a*(K*(1/2 : ℝ)^n))*(R*r^n)^2 at he
    calc
      _ ≤ (a*K)*(1/2 : ℝ)^n*(R*r^n)^2 := he.trans_eq (by ring)
      _ ≤ C*(1/2 : ℝ)^n*(R*r^n)^2 := by gcongr

end PowerConvexity
