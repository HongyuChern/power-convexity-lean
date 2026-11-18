import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo
import PowerConvexity.Calculus.HarmonicQuadraticHalfBallFour

/-! # Actual interior Hessian bounds from unit L2 energy.
The actual weak harmonic solution is first regularized by the proved
representative theorem. Moser gives its actual value bound; the exact
Poisson Hessian estimate then yields a universal inner Hessian bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_identity_weak_normalized_L2_hessian_bound_two :
    ∃ M > 0, ∀ u : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 u →
      ContinuousOn u (ball (0 : F) 1) →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∀ z ∈ closedBall (0 : F) (1/8 : ℝ), ‖realHessian u z‖ ≤ M := by
  obtain ⟨C,hC,hMoser⟩ := actual_continuous_weak_unitBall_L2_bound_two
    (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1))
  obtain ⟨M0,hM0,hHessian⟩ := classical_harmonic_unitBall_hessian_universal_bound_four
  let B := C+1
  have hB : 0 < B := by dsimp only [B]; linarith
  refine ⟨16*B*M0,by positivity,?_⟩
  intro u hu hc uw hnorm z hz
  have hharm := actual_identity_weak_continuous_is_classical_two isOpen_ball hu hc
  let G : F → ℝ := fun x => B⁻¹*u ((1/4 : ℝ) • x)
  have hmaps (x : F) (hx : x ∈ closedBall (0 : F) 1) :
      (1/4 : ℝ) • x ∈ ball (0 : F) (1/2 : ℝ) := by
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
    linarith
  have hGc : ContinuousOn G (closedBall (0 : F) 1) := by
    apply continuousOn_const.mul
    exact hc.comp (by fun_prop : ContinuousOn (fun x : F => (1/4 : ℝ) • x) (closedBall 0 1))
      (fun x hx => ball_subset_ball (by norm_num) (hmaps x hx))
  have hGh : InnerProductSpace.HarmonicOnNhd G (ball (0 : F) 1) := by
    have hd := classical_harmonic_dilate_to_unitBall_four (by norm_num : (0:ℝ)<1/4)
      (hharm.mono (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1)))
    have he : G = B⁻¹ • (fun x : F => u ((1/4 : ℝ) • x)) := rfl
    rw [he]
    exact hd.const_smul
  have hGb (x : F) (hx : x ∈ closedBall (0 : F) 1) : |G x| ≤ 1 := by
    have hm := hMoser u hu (hc.mono (ball_subset_ball (by norm_num))) uw _ (hmaps x hx)
    have hb : |u ((1/4 : ℝ) • x)| ≤ B :=
      hm.trans ((mul_le_mul_of_nonneg_left hnorm hC).trans (by dsimp only [B]; linarith))
    change |B⁻¹*u ((1/4 : ℝ) • x)| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hB)]
    calc
      B⁻¹*|u ((1/4 : ℝ) • x)| ≤ B⁻¹*B := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have hz4 : (4 : ℝ) • z ∈ closedBall (0 : F) (1/2 : ℝ) := by
    have hn : ‖z‖ ≤ 1/8 := by simpa only [mem_closedBall,dist_zero_right] using hz
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4)]
    linarith
  have hzU : z ∈ ball (0 : F) 1 := closedBall_subset_ball (by norm_num) hz
  have hh := hHessian G hGc hGh hGb _ hz4
  have he : realHessian G ((4 : ℝ) • z) = (B⁻¹*(1/16 : ℝ)) • realHessian u z := by
    change realHessian (fun x => B⁻¹*u ((1/4 : ℝ) • x)) ((4 : ℝ) • z) = _
    rw [CHS.Calculus.realHessian_const_mul,actual_realHessian_comp_scalar_four (1/4)
      (by simpa only [smul_smul,show (1/4 : ℝ)*4=1 by norm_num,one_smul] using (hharm z hzU).1)]
    norm_num [smul_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < B⁻¹*(1/16 : ℝ))] at hh
  calc
    ‖realHessian u z‖ = (16*B)*((B⁻¹*(1/16 : ℝ))*‖realHessian u z‖) := by
      field_simp
      <;> ring
    _ ≤ (16*B)*M0 := mul_le_mul_of_nonneg_left hh (by positivity)

end PowerConvexity
