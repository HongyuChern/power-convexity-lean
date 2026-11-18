import PowerConvexity.Analysis.ActualFlatDriftClosedDataFour
import PowerConvexity.Analysis.ActualFlatDriftQuadraticImprovementFour
import PowerConvexity.Analysis.ActualFlatDriftFrozenCorrectionFour
import PowerConvexity.Analysis.ActualHalfspaceQuadraticAbsoluteBoundFour

/-! # Actual quadratic improvement satisfying the full frozen drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_frozen_quadratic_improvement_four
    {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda) :
    ∃ M > 0, ∀ eta > 0, ∀ Rmax > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r ≤ Rmax ∧
      ∃ K > 0, ∀ N : E, ‖N‖=1 → ∃ delta > 0, delta ≤ 1 ∧
      ∀ D : ActualFlatDriftPerturbationDataFour N lam Lambda delta,
      ContinuousOn D.drift (actualFlatClosedUpperBallFour N 1) →
      ContinuousOn D.source (actualFlatClosedUpperBallFour N 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (realBlockHessian realDirections imagDirections q 0).trace+
          fderiv ℝ q 0 (D.drift 0) = -D.source 0 ∧
        ‖fderiv ℝ q 0‖ ≤ K ∧ (∀ x, ‖realHessian q x‖ ≤ M+eta) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |D.solution x-q x| ≤ eta*r^2 := by
  obtain ⟨M,hM,ha⟩ := actual_flat_drift_quadratic_improvement_four hlam hLambda
  refine ⟨M,hM,?_⟩
  intro eta heta Rmax hRmax
  obtain ⟨r,hr,hr8,hrmax,hstep⟩ := ha (eta/2) (half_pos heta) Rmax hRmax
  let K := 68*(1+(eta/2)*r^2)/r
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨r,hr,hr8,hrmax,K,hK,?_⟩
  intro N hN
  obtain ⟨delta0,hd0,hd01,hbase⟩ := hstep N hN
  let delta := min delta0 (eta/(1+K))
  have hd : 0 < delta := lt_min hd0 (div_pos heta (by positivity))
  have hdd0 : delta ≤ delta0 := min_le_left _ _
  have hdeta : delta*(1+K) ≤ eta :=
    (le_div_iff₀ (by positivity : 0 < 1+K)).mp (min_le_right _ _)
  refine ⟨delta,hd,hdd0.trans hd01,?_⟩
  intro D hbc hfc
  obtain ⟨p,hp,hp0,hpt,hpH,hpa⟩ := hbase (actualFlatDriftPerturbationDataFour_weaken D hdd0)
  change ∀ x ∈ actualFlatClosedUpperBallFour N r, |D.solution x-p x| ≤ (eta/2)*r^2 at hpa
  have hpb : ∀ x : E, 0 ≤ inner ℝ N x → ‖x-(0 : E)‖ ≤ r → |p x| ≤ 1+(eta/2)*r^2 := by
    intro x hx hxr
    have hxc : x ∈ actualFlatClosedUpperBallFour N r :=
      ⟨by simpa only [mem_closedBall,dist_eq_norm] using hxr,hx⟩
    have hxu : x ∈ actualFlatClosedUpperBallFour N 1 :=
      ⟨closedBall_subset_closedBall (hr8.trans (by norm_num)) hxc.1,hx⟩
    calc
      |p x| = |D.solution x-(D.solution x-p x)| := by congr 1; ring
      _ ≤ |D.solution x|+|D.solution x-p x| := abs_sub _ _
      _ ≤ 1+(eta/2)*r^2 := add_le_add (D.solution_bound x hxu) (hpa x hxc)
  have hpD : ‖fderiv ℝ p 0‖ ≤ K :=
    actual_halfspace_quadratic_absolute_gradient_four hN (by simp) hr (by positivity) hp hpb
  obtain ⟨hb0,hf0⟩ := actual_flat_drift_data_boundary_bounds_four hN D hbc hfc
  have hc : delta*(1+‖fderiv ℝ p 0‖) ≤ eta :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hpD) hd.le).trans hdeta
  let q := actualFlatDriftCorrectedPolynomialFour N (D.drift 0) (D.source 0) p
  have hqD : fderiv ℝ q 0=fderiv ℝ p 0 := actual_flat_drift_corrected_first_jet_four _ _ _ hp
  have hqH (x : E) : ‖realHessian q x-realHessian p x‖ ≤ eta :=
    (actual_flat_drift_correction_hessian_bound_four hN hf0 hb0 hp x).trans hc
  have hqv (x : E) : |q x-p x| ≤ (eta/2)*‖x‖^2 :=
    (actual_flat_drift_correction_value_bound_four hN hf0 hb0 p x).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc (by norm_num)) (sq_nonneg _))
  refine ⟨q,actual_flat_drift_corrected_quadratic_four _ _ _ hp,
    fun x hx => actual_flat_drift_corrected_zero_four _ _ _ hp0 hx,
    actual_flat_drift_corrected_frozen_equation_four hN _ _ hp (hpt 0),
    ?_,?_,?_⟩
  · rw [hqD]
    exact hpD
  · intro x
    calc
      ‖realHessian q x‖ = ‖(realHessian q x-realHessian p x)+realHessian p x‖ := by
        congr 1; abel
      _ ≤ ‖realHessian q x-realHessian p x‖+‖realHessian p x‖ :=
        norm_add_le (realHessian q x-realHessian p x) (realHessian p x)
      _ ≤ eta+M := add_le_add (hqH x) (hpH x)
      _ = M+eta := by ring
  · intro x hx
    have hxn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    have hsq : ‖x‖^2 ≤ r^2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
    have hqa : |p x-q x| ≤ (eta/2)*r^2 := by
      rw [abs_sub_comm]
      exact (hqv x).trans (mul_le_mul_of_nonneg_left hsq (half_pos heta).le)
    calc
      |D.solution x-q x| ≤ |D.solution x-p x|+|p x-q x| := abs_sub_le _ _ _
      _ ≤ (eta/2)*r^2+(eta/2)*r^2 := add_le_add (hpa x hx) hqa
      _ = eta*r^2 := by ring

end PowerConvexity
