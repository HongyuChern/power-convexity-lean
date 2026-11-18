import PowerConvexity.Analysis.ActualFlatPointwiseRemainderFour

/-! # An actual interior probe ball in overlapping boundary half-balls -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_halfspace_shared_probe_four {N x y : E} (hN : ‖N‖=1)
    (hx : 0 ≤ inner ℝ N x) {s : ℝ} (hs : 0 < s) (hxy : ‖x-y‖ ≤ s/4)
    {w : E} (hw : w ∈ closedBall (0 : E) (s/4)) :
    let z := x+(s/2) • N+w
    0 ≤ inner ℝ N z ∧ ‖z-x‖ ≤ s ∧ ‖z-y‖ ≤ s := by
  have hwN : ‖w‖ ≤ s/4 := by simpa only [mem_closedBall,dist_zero_right] using hw
  have hNs : ‖(s/2) • N‖=s/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hs),hN,mul_one]
  have hi : -(s/4) ≤ inner ℝ N w := by
    have hh := abs_le.mp (by simpa only [hN,one_mul] using abs_real_inner_le_norm N w :
      |inner ℝ N w| ≤ ‖w‖)
    linarith [hh.1]
  refine ⟨?_,?_,?_⟩
  · simp only [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
    linarith
  · have he : x+(s/2) • N+w-x=(s/2) • N+w := by abel
    rw [he]
    have hn := norm_add_le ((s/2) • N) w
    rw [hNs] at hn
    linarith
  · have he : x+(s/2) • N+w-y=(x-y)+(s/2) • N+w := by abel
    rw [he]
    have hn := (norm_add_le ((x-y)+(s/2) • N) w).trans
      (add_le_add (norm_add_le (x-y) ((s/2) • N)) (le_refl ‖w‖))
    rw [hNs] at hn
    linarith

theorem actual_quadratic_gradient_from_scaled_sup_four {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hb : ∀ x ∈ closedBall (0 : E) r, |q x| ≤ K*r^2) :
    ‖fderiv ℝ q 0‖ ≤ K*r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hK hr.le)
  intro v hv
  have hp : r • v ∈ closedBall (0 : E) r := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one,le_refl]
  have hm : -(r • v) ∈ closedBall (0 : E) r := by
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using hp
  have ht1 := quadratic_exact_Taylor hq 0 (r • v)
  have ht2 := quadratic_exact_Taylor hq 0 (-(r • v))
  have he : q (r • v)-q (-(r • v))=(2*r)*fderiv ℝ q 0 v := by
    rw [ht1,ht2]
    simp only [sub_zero,map_smul,map_neg,_root_.smul_apply,_root_.neg_apply,smul_eq_mul]
    ring
  have hh := (abs_sub (q (r • v)) (q (-(r • v)))).trans (add_le_add (hb _ hp) (hb _ hm))
  rw [he,abs_mul,abs_of_pos (by positivity : 0 < 2*r)] at hh
  rw [Real.norm_eq_abs]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*r)).mp
  nlinarith only [hh]

theorem actual_quadratic_scaled_sup_jets_at_four {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (c : E) {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hb : ∀ w ∈ closedBall (0 : E) r, |q (c+w)| ≤ K*r^2) :
    |q c| ≤ K*r^2 ∧ ‖fderiv ℝ q c‖ ≤ K*r ∧ ‖realHessian q c‖ ≤ 8*K := by
  have hqt : IsQuadraticPolynomial (fun w => q (c+w)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      IsQuadraticPolynomial_comp_affine hq (ContinuousLinearMap.id ℝ E) c
  have hv := hb 0 (mem_closedBall_self hr.le)
  have hd := actual_quadratic_gradient_from_scaled_sup_four hqt hr hK hb
  have hh := quadratic_hessian_norm_bound_from_scaled_sup hqt hr hK hb
  obtain ⟨hD,hH⟩ := actual_quadratic_translate_jets_two hq c
  simpa only [add_zero,hD,hH] using And.intro hv (And.intro hd hh)

end PowerConvexity
