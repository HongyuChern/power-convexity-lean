import PowerConvexity.Analysis.ActualFlatDriftPhysicalNormalizationFour
import PowerConvexity.Analysis.ActualFlatDriftPrescribedHolderGeneralFour
import PowerConvexity.Analysis.ActualFlatDriftGeneralFrozenUpdateFour

/-! # Quantitative boundary expansion on a genuine physical scale with drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_prescribed_holder_physical_expansion_four
    {lam Lambda alpha Ka Kb Kf Bd B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKf : 0 ≤ Kf) (hBd : 0 ≤ Bd)
    (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧ ∃ C > 0,
      ∀ D : ActualFlatDriftPhysicalInputFour N lam Lambda alpha Ka Kb Kf Bd B, |D.source 0| ≤ F →
      ∃ P : E → ℝ, IsQuadraticPolynomial P ∧
        (∀ x : E, inner ℝ N x=0 → P x=0) ∧
        (realBlockHessian realDirections imagDirections P 0).trace+
          fderiv ℝ P 0 (D.drift 0) = -D.source 0 ∧
        ‖fderiv ℝ P 0‖ ≤ C ∧ (∀ x, ‖realHessian P x‖ ≤ C) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (R*r^n),
          |D.solution x-P x| ≤ C*(r^alpha)^n*(R*r^n)^2 := by
  obtain ⟨K,hK,r,hr,hr8,hrp,hexp⟩ := actual_flat_drift_prescribed_holder_general_expansion_four
    hlam hLambda halpha halpha1 (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨r,hr,hr8,hrp,?_⟩
  intro N hN
  obtain ⟨kappa,hk,_,hpoly⟩ := hexp N hN
  obtain ⟨R,hR,hR1,a,ha,ha1,haF,hsize,hca,hcb,hbd,hs⟩ :=
    actual_flat_drift_physical_scale_four halpha halpha1.le hKa hKb hKf hBd hB hF hk
  let C := 1+a*K+a*R*K
  have hC : 0 < C := by dsimp only [C]; positivity
  have haK : a*K ≤ C := by dsimp only [C]; nlinarith [mul_nonneg (mul_nonneg ha.le hR.le) hK.le]
  have haRK : a*R*K ≤ C := by dsimp only [C]; nlinarith [mul_nonneg ha.le hK.le]
  refine ⟨R,hR,hR1,C,hC,?_⟩
  intro D hf0
  let D' := actualFlatDriftPhysicalNormalizeFour hR hR1 ha hKb D hca hcb hbd hs hsize
  have hf' : |D'.source 0| ≤ (1 : ℝ) := by
    change |actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source (fun _ => 0) R a 0| ≤ 1
    rw [actual_flat_drift_zero_residual_source_four,smul_zero,abs_mul,abs_of_pos (inv_pos.mpr ha)]
    exact (mul_le_mul_of_nonneg_left hf0 (inv_pos.mpr ha).le).trans
      (by rw [inv_mul_eq_div]; exact (div_le_one ha).mpr haF)
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := hpoly D' hf'
  change ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
    |normalizedScalarResidualTwo D.solution (fun _ => 0) R a x-p x| ≤
      K*(r^alpha)^n*(r^n)^2 at herr
  have hq : IsQuadraticPolynomial (fun _ : E => (0 : ℝ)) := (quadraticSubmodule E).zero_mem
  have hDz : fderiv ℝ (fun _ : E => (0 : ℝ)) 0=0 := by simp
  have hHz (x : E) : realHessian (fun _ : E => (0 : ℝ)) x=0 := by unfold realHessian; simp
  have hTz : (realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) 0).trace=0 := by
    simp only [realBlockHessian,Matrix.trace,Matrix.diag,hHz,_root_.zero_apply,Finset.sum_const_zero]
  have hpfreeze : (realBlockHessian realDirections imagDirections p 0).trace+fderiv ℝ p 0 (R • D.drift 0) =
      -a⁻¹*(D.source 0+(realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) 0).trace+
        fderiv ℝ (fun _ : E => (0 : ℝ)) 0 (D.drift 0)) := by
    change (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (R • D.drift (R • (0 : E))) =
      -actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source (fun _ => 0) R a 0 at hpt
    simpa only [actual_flat_drift_zero_residual_source_four,smul_zero,hTz,hDz,_root_.zero_apply,
      add_zero,neg_mul] using hpt
  let P := scalarQuadraticUpdateTwo (fun _ => 0) p R a
  obtain ⟨_,hinc1,hinc2⟩ := scalarQuadraticUpdateTwo_jet_increment_bounds hq hp hR ha.le
    (show |p 0| ≤ K by rw [hp0 0 (by simp),abs_zero]; exact hK.le) hpD (hpH 0)
  have hPD : ‖fderiv ℝ P 0‖ ≤ C := by
    change ‖fderiv ℝ P 0-fderiv ℝ (fun _ : E => (0 : ℝ)) 0‖ ≤ a*R*K at hinc1
    rw [hDz,sub_zero] at hinc1
    exact hinc1.trans haRK
  refine ⟨P,scalarQuadraticUpdateTwo_isQuadratic hq hp R a,
    actual_flat_quadratic_update_zero_four hR (fun _ _ => rfl) hp0,
    actual_flat_drift_quadratic_update_general_frozen_four hq hp hR ha _ _ hpfreeze,hPD,?_,?_⟩
  · intro x
    have hh := hinc2 x
    change ‖realHessian P x-realHessian (fun _ : E => (0 : ℝ)) x‖ ≤ a*K at hh
    rw [hHz] at hh
    have he : realHessian P x-(0 : E →L[ℝ] E →L[ℝ] ℝ)=realHessian P x := by ext v w; simp
    rw [he] at hh
    exact hh.trans haK
  · intro n x hx
    have he := actual_flat_physical_residual_error_four hR ha (herr n) x hx
    change |D.solution x-P x| ≤ (a*(K*(r^alpha)^n))*(R*r^n)^2 at he
    calc
      _ ≤ (a*K)*(r^alpha)^n*(R*r^n)^2 := he.trans_eq (by ring)
      _ ≤ C*(r^alpha)^n*(R*r^n)^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right haK (by positivity)) (sq_nonneg _)

end PowerConvexity
