import PowerConvexity.Calculus.SecondTaylorHessianModulus
import PowerConvexity.Algebra.BilinearNormFromQuadratic

/-! # Actual quadratic Hessian bounds from values on a closed ball.
An exact central difference gives the diagonal bound. Homogeneity and real
polarization then bound the actual continuous bilinear operator norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem IsQuadraticPolynomial_sub {q p : V → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) :
    IsQuadraticPolynomial (fun x => q x-p x) := by
  have he : (fun x => q x-p x) = q+(fun x => (-1)*p x) := by funext x; simp [sub_eq_add_neg]
  rw [he]
  exact IsQuadraticPolynomial_add hq (IsQuadraticPolynomial_const_mul hp (-1))

theorem quadratic_central_second_difference_zero {q : V → ℝ}
    (hq : IsQuadraticPolynomial q) (R : ℝ) (v : V) :
    q (R • v)+q (-(R • v))-2*q 0 = R^2*realHessian q 0 v v := by
  have hp := quadratic_exact_Taylor hq 0 (R • v)
  have hn := quadratic_exact_Taylor hq 0 (-(R • v))
  rw [hp,hn]
  simp only [sub_zero,map_smul,map_neg,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply,smul_eq_mul]
  ring

theorem quadratic_hessian_unit_bound_from_scaled_sup {q : V → ℝ} {R K : ℝ}
    (hq : IsQuadraticPolynomial q) (hR : 0 < R)
    (hb : ∀ x ∈ closedBall (0 : V) R, |q x| ≤ K*R^2)
    (v : V) (hv : ‖v‖ = 1) : |realHessian q 0 v v| ≤ 4*K := by
  have hp : R • v ∈ closedBall (0 : V) R := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hv,mul_one,le_refl]
  have hn : -(R • v) ∈ closedBall (0 : V) R := by
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using hp
  have h0 := abs_le.mp (hb 0 (mem_closedBall_self hR.le))
  have hpb := abs_le.mp (hb _ hp)
  have hnb := abs_le.mp (hb _ hn)
  have hh : |q (R • v)+q (-(R • v))-2*q 0| ≤ R^2*(4*K) :=
    abs_le.mpr ⟨by nlinarith only [hpb.1,hnb.1,h0.2],by nlinarith only [hpb.2,hnb.2,h0.1]⟩
  rw [quadratic_central_second_difference_zero hq,abs_mul,abs_of_pos (sq_pos_of_pos hR)] at hh
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).mp hh

theorem quadratic_hessian_norm_bound_from_scaled_sup {q : V → ℝ} {R K : ℝ}
    (hq : IsQuadraticPolynomial q) (hR : 0 < R) (hK : 0 ≤ K)
    (hb : ∀ x ∈ closedBall (0 : V) R, |q x| ≤ K*R^2) : ‖realHessian q 0‖ ≤ 8*K := by
  have hu := quadratic_hessian_unit_bound_from_scaled_sup hq hR hb
  have hup := bilinear_quadratic_upper_from_unit_bound (realHessian q 0)
    (fun v hv => (le_abs_self _).trans (hu v hv))
  have hdown := bilinear_quadratic_upper_from_unit_bound (-realHessian q 0)
    (fun v hv => by
      change -realHessian q 0 v v ≤ 4*K
      exact (neg_le_abs _).trans (hu v hv))
  have hquad (v : V) : |realHessian q 0 v v| ≤ (4*K)*‖v‖^2 := by
    apply abs_le.mpr
    refine ⟨?_,hup v⟩
    have hh := hdown v
    change -realHessian q 0 v v ≤ (4*K)*‖v‖^2 at hh
    linarith only [hh]
  have hh := symmetric_bilinear_norm_le_of_quadratic_abs_bound (realHessian q 0)
    (realHessian_symm (IsQuadraticPolynomial_contDiff hq 2).contDiffAt) (by positivity) hquad
  exact hh.trans_eq (by ring)

end PowerConvexity
