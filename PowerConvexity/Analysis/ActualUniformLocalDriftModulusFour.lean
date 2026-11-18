import PowerConvexity.Analysis.ActualLocalDriftRadiusFour

/-! # A genuine common interior modulus for the full drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_classical_local_drift_modulus_four
    {U : Set E} (hU : IsOpen U) (A : ℕ → NormalizedEllipticCoeff (2+2) U)
    {L M B F : ℝ} (hL : ∀ n, (A n).1.Λ ≤ L) (hM : 0 ≤ M) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hA : ∀ n i j, ContDiffOn ℝ 1 (fun y => (A n).1.a y i j) U)
    (b : ℕ → E → E) (hb : ∀ n, ContinuousOn (b n) U)
    (hdiv : ∀ n x, x ∈ U → actualCoefficientColumnDivergenceFour (A n).1.a x=b n x)
    (htrace : ∀ n x, x ∈ U → 1 ≤ ((A n).1.a x).trace)
    (hbb : ∀ n x, x ∈ U → ‖b n x‖ ≤ B)
    (f u : ℕ → E → ℝ) (hf : ∀ n, ContinuousOn (f n) U) (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hub : ∀ n x, x ∈ U → |u n x| ≤ M) (hfb : ∀ n x, x ∈ U → |f n x| ≤ F)
    (hpde : ∀ n x, x ∈ U → (∑ i, ∑ j, (A n).1.a x i j*euclideanHessian (u n) x i j)+
      fderiv ℝ (u n) x (b n x) = -f n x) :
    ∀ x ∈ U, ∀ eps > 0, ∃ delta > 0,
      ∀ n y, y ∈ U → dist y x < delta → |u n y-u n x| < eps := by
  intro x hx eps heps
  obtain ⟨r,hr,hr1,hclosed,hrB,herr⟩ := actual_local_drift_error_radius_four hU hx hB hF heps
  let beta := actualUniformMoserExponentFour L
  let C := actualUniformMoserBoundFour L (M+(F+1))
  have hbeta : 0 < beta := Real.exp_pos _
  have hC0 : 0 ≤ CHolderMoser (2+2) :=
    (C_harnack_nonneg (by norm_num : 2 < ((2+2 : ℕ) : ℝ))).trans C_harnack_le_C_holder_Moser
  have hL0 : 0 ≤ L := (A 0).1.Λ_nonneg.trans (hL 0)
  have hCb : actualUniformMoserBoundFour L (M+r^2*(F+1)) ≤ C := by
    have hr2 : r^2 ≤ 1 := by nlinarith
    have hh : M+r^2*(F+1) ≤ M+(F+1) := by nlinarith
    dsimp only [C,actualUniformMoserBoundFour]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hcont : ContinuousAt (fun y : E => C*‖r⁻¹ • (y-x)‖^beta) x :=
    continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).const_smul r⁻¹).norm.rpow_const
      (Or.inr hbeta.le))
  have hlim : Tendsto (fun y : E => C*‖r⁻¹ • (y-x)‖^beta) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self,smul_zero,norm_zero,Real.zero_rpow hbeta.ne',mul_zero] using hcont.tendsto
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp ((tendsto_order.1 hlim).2 (eps/2) (half_pos heps))
  refine ⟨min d (r/2),lt_min hd (half_pos hr),?_⟩
  intro n y _ hxy
  let z : E := r⁻¹ • (y-x)
  have hz : z ∈ ball (0 : E) (1/2 : ℝ) := by
    simp only [mem_ball,dist_zero_right,z,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),← dist_eq_norm]
    have hh := hxy.trans_le (min_le_right d (r/2))
    calc
      r⁻¹*dist y x = dist y x/r := by ring
      _ < 1/2 := (div_lt_iff₀ hr).mpr (by linarith)
  have hrep : x+r • z=y := by
    dsimp only [z]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
  have hosc := actual_local_classical_drift_oscillation_four hU (A n) (hL n) hM
    (by linarith : 0 < F+1) (hA n) (hb n) (hdiv n) (htrace n) (hbb n) (hf n) (hu n)
    (hub n) (fun y hy => (hfb n y hy).trans (by linarith)) (hpde n) hr hclosed hrB
    z hz 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1/2))
  rw [hrep,smul_zero,add_zero,sub_zero] at hosc
  have hh : C*‖z‖^beta < eps/2 := hball (hxy.trans_le (min_le_left d (r/2)))
  have hmul := mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg (norm_nonneg z) beta)
  change actualUniformMoserBoundFour L (M+r^2*(F+1))*‖z‖^beta ≤ C*‖z‖^beta at hmul
  change |u n y-u n x| ≤ 2*(r^2*(F+1))+actualUniformMoserBoundFour L (M+r^2*(F+1))*‖z‖^beta at hosc
  nlinarith

end PowerConvexity
