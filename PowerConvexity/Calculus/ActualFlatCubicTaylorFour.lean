import PowerConvexity.Calculus.HarmonicCubicTaylorFour
import PowerConvexity.Calculus.ActualFlatHalfRadiusTaylorFour

/-! # Uniform cubic boundary Taylor error for the actual harmonic odd extension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_harmonic_flat_boundary_cubic_taylor_four :
    ∃ M > 0, ∃ L > 0, ∀ N : E, ‖N‖=1 → ∀ u : E → ℝ,
      ContinuousOn u (actualFlatClosedUpperBallFour N 1) →
      InnerProductSpace.HarmonicOnNhd u (actualFlatUpperBallFour N 1) →
      (∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ r : ℝ, 0 < r → r ≤ (1/4 : ℝ) →
          ∀ x ∈ actualFlatClosedUpperBallFour N r, |u x-q x| ≤ L*r^3 := by
  obtain ⟨M,hM,L,hL,ha⟩ := classical_harmonic_unitBall_universal_cubic_taylor_four
  refine ⟨M,hM,L,hL,?_⟩
  intro N hN u huC huH hu0 hub
  let v := actualFlatOddExtensionFour N u
  obtain ⟨hvC,hvH,hvreg⟩ := actual_zero_flat_harmonic_odd_reflection_four hN huC huH hu0
  have hvb (x : E) (hx : x ∈ closedBall (0 : E) 1) : |v x| ≤ 1 := by
    by_cases hn : 0 ≤ inner ℝ N x
    · rw [show v x=u x from actualFlatOddExtensionFour_upper N u hn]
      exact hub x ⟨hx,hn⟩
    · change |if 0 ≤ inner ℝ N x then u x else -u (actualFlatReflectionFour N x)| ≤ 1
      rw [if_neg hn,abs_neg]
      apply hub
      refine ⟨?_,?_⟩
      · simpa only [mem_closedBall,dist_zero_right,(actualFlatReflectionFour N).norm_map] using hx
      · change 0 ≤ inner ℝ N (actualFlatReflectionFour N x)
        rw [actualFlatReflectionFour_normal hN]
        exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hn))
  obtain ⟨hqp,hqt,hqH,hqe⟩ := ha v hvC hvH hvb
  have hv2 : ContDiffAt ℝ 2 v 0 := (hvH 0 (mem_ball_self (by norm_num))).1
  have ho : (fun x => v (actualFlatReflectionFour N x)) =ᶠ[𝓝 (0 : E)] (fun x => -v x) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ)<1))] with x hx
    exact actualFlatOddExtensionFour_odd hN u hu0 (ball_subset_closedBall hx)
  refine ⟨secondTaylorPolynomialZero v,hqp,
    actual_secondTaylor_flat_zero_of_odd_four hN hv2 ho,hqt,?_,?_⟩
  · intro x
    rw [secondTaylorPolynomialZero_hessian hv2]
    exact hqH
  · intro r hr hrq x hx
    have hh := hqe r hr (hrq.trans (by norm_num)) x hx.1
    rw [show v x=u x from actualFlatOddExtensionFour_upper N u hx.2] at hh
    exact hh

theorem actual_harmonic_flat_half_boundary_cubic_taylor_four :
    ∃ M > 0, ∃ L > 0, ∀ N : E, ‖N‖=1 → ∀ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) →
      InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) →
      (∀ x ∈ closedBall (0 : E) (1/2), inner ℝ N x=0 → g x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ r : ℝ, 0 < r → r ≤ (1/8 : ℝ) →
          ∀ x ∈ actualFlatClosedUpperBallFour N r, |g x-q x| ≤ L*r^3 := by
  obtain ⟨M,hM,L,hL,ha⟩ := actual_harmonic_flat_boundary_cubic_taylor_four
  refine ⟨4*M,by positivity,8*L,by positivity,?_⟩
  intro N hN g hgC hgH hg0 hgb
  let G : E → ℝ := fun x => g ((1/2 : ℝ) • x)
  have hmapC : MapsTo (fun x : E => (1/2 : ℝ) • x)
      (actualFlatClosedUpperBallFour N 1) (actualFlatClosedUpperBallFour N (1/2)) := by
    intro x hx
    constructor
    · have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith
    · change 0 ≤ inner ℝ N ((1/2 : ℝ) • x)
      rw [inner_smul_right]
      exact mul_nonneg (by norm_num) hx.2
  have hmapU : MapsTo (fun x : E => (1/2 : ℝ) • x)
      (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N (1/2)) := by
    intro x hx
    constructor
    · have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx.1
      simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith
    · change 0 < inner ℝ N ((1/2 : ℝ) • x)
      rw [inner_smul_right]
      exact mul_pos (by norm_num) hx.2
  have hGC : ContinuousOn G (actualFlatClosedUpperBallFour N 1) :=
    hgC.comp (by fun_prop : ContinuousOn (fun x : E => (1/2 : ℝ) • x) _) hmapC
  have hGH : InnerProductSpace.HarmonicOnNhd G (actualFlatUpperBallFour N 1) := by
    have hh := classical_harmonic_affine_scalar_pullback_two
      (actualFlatUpperBallFour_isOpen N (1/2)) hgH (0 : E) (1/2)
    intro x hx
    simpa only [zero_add] using hh x (by simpa only [mem_preimage,zero_add] using hmapU hx)
  have hG0 (x : E) (hx : x ∈ closedBall (0 : E) 1) (hn : inner ℝ N x=0) : G x=0 := by
    have hm := hmapC (show x ∈ actualFlatClosedUpperBallFour N 1 from ⟨hx,hn.ge⟩)
    apply hg0 _ hm.1
    simp only [inner_smul_right,hn,mul_zero]
  obtain ⟨p,hp,hp0,hpt,hpH,hpa⟩ := ha N hN G hGC hGH hG0 (fun x hx => hgb _ (hmapC hx))
  let q : E → ℝ := fun x => p ((2 : ℝ) • x)
  have hpC := IsQuadraticPolynomial_contDiff hp 2
  have hH (x : E) : realHessian q x = (4 : ℝ) • realHessian p ((2 : ℝ) • x) := by
    simpa only [q,show (2 : ℝ)^2=4 by norm_num] using
      actual_realHessian_comp_scalar_four 2 hpC.contDiffAt (x := x)
  refine ⟨q,IsQuadraticPolynomial_comp_scalar hp 2,?_,?_,?_,?_⟩
  · intro x hx
    apply hp0
    simp only [inner_smul_right,hx,mul_zero]
  · intro x
    change realBlockTraceFormFour (realHessian q x)=0
    rw [hH,map_smul]
    change (4 : ℝ)*(realBlockHessian realDirections imagDirections p ((2 : ℝ) • x)).trace=0
    rw [hpt,mul_zero]
  · intro x
    rw [hH,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<4)]
    exact mul_le_mul_of_nonneg_left (hpH _) (by norm_num)
  · intro r hr hr8 x hx
    have hx2 : (2 : ℝ) • x ∈ actualFlatClosedUpperBallFour N (2*r) := by
      constructor
      · have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx.1
        simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ)<2)]
        linarith
      · change 0 ≤ inner ℝ N ((2 : ℝ) • x)
        rw [inner_smul_right]
        exact mul_nonneg (by norm_num) hx.2
    have hh := hpa (2*r) (by positivity) (by linarith) _ hx2
    simp only [G,smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul] at hh
    exact hh.trans_eq (by ring)

end PowerConvexity
