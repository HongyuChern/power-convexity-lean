import PowerConvexity.Calculus.HarmonicUniversalQuadraticApproximationFour

/-! # The uniform approximation on the actual compactness half ball.
The input is exactly the regularity and bound of the actual normalized CMA limit.
All scalar pullback factors in the actual Hessian and error are retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem IsQuadraticPolynomial_comp_scalar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : V → ℝ} (hq : IsQuadraticPolynomial q) (r : ℝ) :
    IsQuadraticPolynomial (fun x => q (r • x)) := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  refine ⟨c,r • l,r^2 • H,?_,?_⟩
  · intro v w
    simp only [_root_.smul_apply,smul_eq_mul,hs v w]
  · intro x
    change q (r • x) = c+(r • l) x+(r^2 • H) x x
    rw [he]
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    ring

theorem actual_realHessian_comp_scalar_four {g : E → ℝ} {x : E} (r : ℝ)
    (hg : ContDiffAt ℝ 2 g (r • x)) :
    realHessian (fun y => g (r • y)) x = r^2 • realHessian g (r • x) := by
  ext v w
  have h := realHessian_comp_affine (r • ContinuousLinearMap.id ℝ E) (0 : E)
    (by simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hg) v w
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add,
    map_smul,_root_.smul_apply,smul_eq_mul] at h ⊢
  rw [h]
  ring

theorem classical_harmonic_dilate_to_unitBall_four {g : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hg : InnerProductSpace.HarmonicOnNhd g (ball (0 : E) R)) :
    InnerProductSpace.HarmonicOnNhd (fun x => g (R • x)) (ball (0 : E) 1) := by
  have hh := classical_harmonic_affine_scalar_pullback_two isOpen_ball hg (0 : E) R
  intro x hx
  have hm : (0 : E)+R • x ∈ ball 0 R := by
    have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    simpa only [zero_add,mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR,mul_one] using
      mul_lt_mul_of_pos_left hn hR
  simpa only [zero_add] using hh x hm

theorem continuous_dilate_to_closed_unitBall_four {g : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hgc : ContinuousOn g (closedBall (0 : E) R)) :
    ContinuousOn (fun x => g (R • x)) (closedBall (0 : E) 1) := by
  have hcmap : Continuous (fun x : E => R • x) := by fun_prop
  change ContinuousOn (g ∘ (fun x : E => R • x)) (closedBall 0 1)
  apply hgc.comp hcmap.continuousOn
  intro x hx
  have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
  simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR,mul_one] using
    mul_le_mul_of_nonneg_left hn hR.le

theorem classical_harmonic_halfBall_universal_quadratic_approximation_four :
    ∃ M > 0, ∀ η > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧
      ∀ g : E → ℝ, ContinuousOn g (closedBall 0 (1/2 : ℝ)) →
        InnerProductSpace.HarmonicOnNhd g (ball 0 (1/2 : ℝ)) →
        (∀ x ∈ closedBall (0 : E) (1/2 : ℝ), |g x| ≤ 1) →
        ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
          (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
          (∀ x, ‖realHessian q x‖ ≤ M) ∧
          ∀ x ∈ closedBall (0 : E) r, |g x-q x| ≤ η*r^2 := by
  obtain ⟨M,hM,happrox⟩ := classical_harmonic_unitBall_universal_quadratic_approximation_four
  refine ⟨4*M,mul_pos (by norm_num) hM,?_⟩
  intro η hη
  obtain ⟨ρ,hρ,hρq,hρapprox⟩ := happrox (η/4) (by positivity)
  refine ⟨ρ/2,half_pos hρ,by linarith,?_⟩
  intro g hgc hg hgb
  let G : E → ℝ := fun x => g ((1/2 : ℝ) • x)
  have hGC : ContinuousOn G (closedBall 0 1) := continuous_dilate_to_closed_unitBall_four (by norm_num) hgc
  have hGH : InnerProductSpace.HarmonicOnNhd G (ball 0 1) := classical_harmonic_dilate_to_unitBall_four (by norm_num) hg
  have hGb (x : E) (hx : x ∈ closedBall (0 : E) 1) : |G x| ≤ 1 := by
    apply hgb
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith
  obtain ⟨hq,ht,hH,ha⟩ := hρapprox G hGC hGH hGb
  let q : E → ℝ := fun x => secondTaylorPolynomialZero G ((2 : ℝ) • x)
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  refine ⟨q,IsQuadraticPolynomial_comp_scalar hq 2,?_,?_,?_⟩
  · intro x
    have hh := actual_C2_block_trace_affine_scalar_two (c := (0 : E)) (r := 2) (x := x)
      (by simpa only [zero_add] using hqC.contDiffAt (x := (2 : ℝ) • x))
    simpa only [zero_add,ht,mul_zero] using hh
  · intro x
    have hG0 := (hGH 0 (mem_ball_self (by norm_num))).1
    change ‖realHessian (fun y => secondTaylorPolynomialZero G ((2 : ℝ) • y)) x‖ ≤ 4*M
    rw [actual_realHessian_comp_scalar_four 2 hqC.contDiffAt,
      secondTaylorPolynomialZero_hessian hG0,norm_smul,Real.norm_eq_abs]
    simpa only [show (2:ℝ)^2=4 by norm_num,abs_of_pos (by norm_num : (0:ℝ)<4)] using
      (mul_le_mul_of_nonneg_left hH (by norm_num : (0:ℝ) ≤ 4))
  · intro x hx
    have hxρ : (2 : ℝ) • x ∈ closedBall (0 : E) ρ := by
      have hn : ‖x‖ ≤ ρ/2 := by simpa only [mem_closedBall,dist_zero_right] using hx
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    have he : G ((2 : ℝ) • x) = g x := by simp [G,smul_smul]
    have ha' := ha ((2 : ℝ) • x) hxρ
    rw [he] at ha'
    convert ha' using 1 <;> ring

end PowerConvexity
