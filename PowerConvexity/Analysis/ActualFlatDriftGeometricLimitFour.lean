import PowerConvexity.Analysis.ActualFlatDriftJetLimitFour
import PowerConvexity.Analysis.ActualFlatDriftPrescribedHolderSequenceFour

/-! # A limiting actual boundary polynomial retaining its geometric contraction -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_geometric_limit_expansion_four
    {N b0 : E} {u : E → ℝ} {f0 r M K C theta : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (htheta : 0 ≤ theta) (htheta2 : theta ≤ (1/2 : ℝ))
    (S : (n : ℕ) → ActualFlatDriftQuadraticStateFour N u b0 f0 (r^n) (theta^n) M K)
    (hS0 : (S 0).polynomial = (fun _ => 0))
    (hi : ∀ n,
      ‖fderiv ℝ (S (n+1)).polynomial 0-fderiv ℝ (S n).polynomial 0‖ ≤ C*theta^n*r^n ∧
      ∀ x, ‖realHessian (S (n+1)).polynomial x-realHessian (S n).polynomial x‖ ≤ C*theta^n) :
    ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
      (∀ x : E, inner ℝ N x=0 → p x=0) ∧
      (realBlockHessian realDirections imagDirections p 0).trace+fderiv ℝ p 0 b0 = -f0 ∧
      ‖fderiv ℝ p 0‖ ≤ 2*C ∧ (∀ x, ‖realHessian p x‖ ≤ 2*C) ∧
      ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
        |u x-p x| ≤ (1+5*C)*theta^n*(r^n)^2 := by
  let Q : ℕ → E → ℝ := fun n => (S n).polynomial
  have hratio : theta*r ≤ (1/2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hr1 htheta).trans (by simpa only [mul_one] using htheta2)
  have hiD (n : ℕ) : ‖fderiv ℝ (Q (n+1)) 0-fderiv ℝ (Q n) 0‖ ≤ C*(theta*r)^n := by
    rw [mul_pow]
    exact (hi n).1.trans_eq (by ring)
  have hiH (n : ℕ) : ‖realHessian (Q (n+1)) 0-realHessian (Q n) 0‖ ≤ C*theta^n := (hi n).2 0
  obtain ⟨l,hl,hlTail⟩ := actual_geometric_increment_limit
    (X := E →L[ℝ] ℝ) (v := fun n => fderiv ℝ (Q n) 0)
    hC (mul_nonneg htheta hr.le) hratio hiD
  obtain ⟨H,hH,hHB⟩ := actual_geometric_increment_limit
    (X := E →L[ℝ] E →L[ℝ] ℝ) (v := fun n => realHessian (Q n) 0)
    hC htheta htheta2 hiH
  let c : ℝ := 0
  have hc : Tendsto (fun n => Q n 0) atTop (𝓝 c) := by
    have he : (fun n => Q n 0) = fun _ : ℕ => (0 : ℝ) := funext (fun n => (S n).zero 0 (by simp))
    rw [he]
    exact tendsto_const_nhds
  have hcB (n : ℕ) : |Q n 0-c| ≤ 2*C*theta^n*(r^n)^2 := by
    rw [show Q n 0=0 from (S n).zero 0 (by simp)]
    simp only [c,sub_self,abs_zero]
    positivity
  have hlB (n : ℕ) : ‖fderiv ℝ (Q n) 0-l‖ ≤ 2*C*theta^n*r^n := by
    simpa only [mul_pow,mul_assoc] using hlTail n
  have hQ (n : ℕ) : IsQuadraticPolynomial (Q n) := (S n).quadratic
  let p := actualQuadraticJetFunctionTwo c l H
  obtain ⟨hp,hp0,hp1,hp2⟩ := actual_quadratic_jet_reconstruction_two c l H
    (actual_realHessian_limit_symmetry_two hQ hH)
  have hpflat (x : E) (hx : inner ℝ N x=0) : p x=0 := by
    have hv := actual_quadratic_jet_limit_value_four hQ hc hl hH x
    have hv0 : Tendsto (fun n => Q n x) atTop (𝓝 (0 : ℝ)) := by
      have he : (fun n => Q n x) = fun _ : ℕ => (0 : ℝ) := funext (fun n => (S n).zero x hx)
      rw [he]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hv hv0
  have hD0 : fderiv ℝ (Q 0) 0=0 := by change fderiv ℝ (S 0).polynomial 0=0; rw [hS0]; simp
  have hHzero : realHessian (Q 0) 0=0 := by
    change realHessian (S 0).polynomial 0=0
    rw [hS0]
    unfold realHessian
    simp
  have hl0 : ‖l‖ ≤ 2*C := by
    have hh := hlB 0
    change ‖fderiv ℝ (Q 0) 0-l‖ ≤ _ at hh
    simpa only [hD0,pow_zero,mul_one,zero_sub,norm_neg] using hh
  have hHz : ‖realHessian (Q 0) 0-H‖=‖H‖ := by
    rw [hHzero]
    have he : (0 : E →L[ℝ] E →L[ℝ] ℝ)-H = -H := by
      ext v w
      simp only [_root_.sub_apply,_root_.zero_apply,_root_.neg_apply]
      ring
    exact (congrArg norm he).trans (norm_neg H)
  have hH0 : ‖H‖ ≤ 2*C := by
    have hh := hHB 0
    change ‖realHessian (Q 0) 0-H‖ ≤ _ at hh
    simpa only [hHz,pow_zero,mul_one] using hh
  refine ⟨p,hp,hpflat,actual_quadratic_limit_frozen_drift_four hQ hH hl b0 f0 c (fun n => (S n).frozen),
    ?_,?_,?_⟩
  · simpa only [p,hp1] using hl0
  · intro x
    simpa only [p,hp2 x] using hH0
  · intro n x hx
    have ht := actual_quadratic_scaled_tail_bound_two (hQ n) hp hC
      (pow_nonneg htheta n) (pow_nonneg hr.le n)
      (by simpa only [hp0] using hcB n)
      (by simpa only [hp1] using hlB n)
      (by simpa only [hp2 0] using hHB n) x hx.1
    calc
      |u x-p x| ≤ |u x-Q n x|+|Q n x-p x| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (u x-Q n x) (Q n x-p x)
      _ ≤ theta^n*(r^n)^2+5*C*theta^n*(r^n)^2 := add_le_add ((S n).error x hx) ht
      _ = _ := by ring

end PowerConvexity
