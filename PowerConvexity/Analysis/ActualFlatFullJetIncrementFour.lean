import PowerConvexity.Analysis.ActualFlatQuadraticSequenceFour
import PowerConvexity.Calculus.ActualFlatQuadraticNormalJetFour
import PowerConvexity.Analysis.ActualScalarQuadraticJetLimitsTwo

/-! # Full jet increments from the actual boundary sequence -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_normal_mem_closedUpperBall_four {N : E} (hN : ‖N‖=1) {R : ℝ}
    (hR : 0 < R) : R • N ∈ actualFlatClosedUpperBallFour N R := by
  constructor
  · simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hN,mul_one,le_refl]
  · change 0 ≤ inner ℝ N (R • N)
    simpa only [inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one] using hR.le

theorem actual_flat_states_gradient_increment_four {N : E} (hN : ‖N‖=1)
    {u : E → ℝ} {R b r M : ℝ} (hR : 0 < R) (hb : 0 < b) (hr : 0 < r) (hr1 : r ≤ 1)
    (S : ActualFlatQuadraticStateFour N u R b M)
    (T : ActualFlatQuadraticStateFour N u (R*r) (b/2) M)
    (hinc : ∀ x : E, ‖realHessian T.polynomial x-realHessian S.polynomial x‖ ≤ b*M) :
    ‖fderiv ℝ T.polynomial 0-fderiv ℝ S.polynomial 0‖ ≤
      b*R*((1+r^2/2+r^2*M/2)/r) := by
  let q : E → ℝ := fun x => T.polynomial x-S.polynomial x
  have hq : IsQuadraticPolynomial q := (quadraticSubmodule E).sub_mem T.quadratic S.quadratic
  have hq0 (x : E) (hx : inner ℝ N x=0) : q x=0 := by
    simp only [q,T.zero x hx,S.zero x hx,sub_self]
  have hqcT := (IsQuadraticPolynomial_contDiff T.quadratic 2).contDiffAt (x := (0 : E))
  have hqcS := (IsQuadraticPolynomial_contDiff S.quadratic 2).contDiffAt (x := (0 : E))
  have hqH : ‖realHessian q 0‖ ≤ b*M := by
    change ‖realHessian (fun x => T.polynomial x-S.polynomial x) 0‖ ≤ _
    rw [realHessian_sub_at hqcT hqcS]
    exact hinc 0
  have hy := actual_flat_normal_mem_closedUpperBall_four hN (mul_pos hR hr)
  have hys : (R*r) • N ∈ actualFlatClosedUpperBallFour N R := by
    exact ⟨closedBall_subset_closedBall (by nlinarith only [hr1,hR.le]) hy.1,hy.2⟩
  have hv : |q ((R*r) • N)| ≤ b*R^2*(1+r^2/2) := by
    have he : q ((R*r) • N) =
        (u ((R*r) • N)-S.polynomial ((R*r) • N))-
        (u ((R*r) • N)-T.polynomial ((R*r) • N)) := by dsimp only [q]; ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (S.error _ hys) (T.error _ hy)).trans_eq (by ring))
  have hh := actual_flat_quadratic_gradient_from_normal_value_four hN hq hq0
    (mul_pos hR hr) hv hqH
  change ‖fderiv ℝ (fun x => T.polynomial x-S.polynomial x) 0‖ ≤ _ at hh
  rw [fderiv_fun_sub (hqcT.differentiableAt (by norm_num)) (hqcS.differentiableAt (by norm_num))] at hh
  exact hh.trans_eq (by field_simp <;> ring)

theorem actual_flat_sequence_fullJet_increments_four {r M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 < M) :
    ∃ C > 0, ∀ N : E, ‖N‖=1 → ∀ u : E → ℝ,
      ∀ S : (n : ℕ) → ActualFlatQuadraticStateFour N u (r^n) ((1/2 : ℝ)^n) M,
      (∀ n : ℕ, ∀ x : E,
        ‖realHessian (S (n+1)).polynomial x-realHessian (S n).polynomial x‖ ≤ (1/2 : ℝ)^n*M) →
      ∀ n : ℕ, ActualScalarQuadraticIncrementTwo C r n
        (S n).polynomial (S (n+1)).polynomial := by
  let J := (1+r^2/2+r^2*M/2)/r
  have hJ : 0 < J := by dsimp only [J]; positivity
  refine ⟨M+J,add_pos hM hJ,?_⟩
  intro N hN u S hinc n
  have he : (1/2 : ℝ)^n/2=(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
  have hg : ‖fderiv ℝ (S (n+1)).polynomial 0-fderiv ℝ (S n).polynomial 0‖ ≤
      (1/2 : ℝ)^n*r^n*J := by
    have hh := actual_flat_states_gradient_increment_four hN (pow_pos hr n)
      (pow_pos (by norm_num : (0 : ℝ)<1/2) n) hr hr1 (S n)
    rw [← (pow_succ r n),he] at hh
    exact hh (S (n+1)) (hinc n)
  refine ⟨?_,?_,?_⟩
  · have hz1 := (S (n+1)).zero 0 (by simp)
    have hz0 := (S n).zero 0 (by simp)
    rw [hz1,hz0,sub_self,abs_zero]
    positivity
  · exact hg.trans (mul_le_mul_of_nonneg_left (by linarith : J ≤ M+J) (by positivity))
  · intro x
    exact (hinc n x).trans (mul_le_mul_of_nonneg_left (by linarith : M ≤ M+J) (by positivity))

end PowerConvexity
