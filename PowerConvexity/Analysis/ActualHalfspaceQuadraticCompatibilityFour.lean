import PowerConvexity.Analysis.ActualHalfspaceQuadraticProbeFour

/-! # Actual Hessian compatibility from overlapping half-ball value expansions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_halfspace_quadratic_hessian_comparison_four {N x y : E}
    (hN : ‖N‖=1) (hx : 0 ≤ inner ℝ N x) {s C : ℝ} (hs : 0 < s)
    (hxy : ‖x-y‖ ≤ s/4) (hC : 0 ≤ C) {u p q : E → ℝ}
    (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q)
    (hpE : ∀ z : E, 0 ≤ inner ℝ N z → ‖z-x‖ ≤ s → |u z-p z| ≤ C*s^2)
    (hqE : ∀ z : E, 0 ≤ inner ℝ N z → ‖z-y‖ ≤ s → |u z-q z| ≤ C*s^2) :
    ‖realHessian p x-realHessian q y‖ ≤ 256*C := by
  let c := x+(s/2) • N
  have hd := IsQuadraticPolynomial_sub hp hq
  have hsup : ∀ w ∈ closedBall (0 : E) (s/4),
      |p (c+w)-q (c+w)| ≤ (32*C)*(s/4)^2 := by
    intro w hw
    obtain ⟨hz,hzx,hzy⟩ := actual_halfspace_shared_probe_four hN hx hs hxy hw
    have ht := abs_sub_le (p (c+w)) (u (c+w)) (q (c+w))
    rw [abs_sub_comm (p (c+w)) (u (c+w))] at ht
    exact (ht.trans (add_le_add (hpE _ hz hzx) (hqE _ hz hzy))).trans_eq (by ring)
  have hh := (actual_quadratic_scaled_sup_jets_at_four hd c (by positivity : 0 < s/4)
    (by positivity : 0 ≤ 32*C) hsup).2.2
  have he : realHessian (fun z => p z-q z) c = realHessian p x-realHessian q y := by
    rw [realHessian_sub_at (IsQuadraticPolynomial_contDiff hp 2).contDiffAt
      (IsQuadraticPolynomial_contDiff hq 2).contDiffAt]
    rw [quadratic_realHessian_from_jet_zero hp c,quadratic_realHessian_from_jet_zero hp x,
      quadratic_realHessian_from_jet_zero hq c,quadratic_realHessian_from_jet_zero hq y]
  rw [he] at hh
  exact hh.trans_eq (by ring)

theorem actual_halfspace_quadratic_field_hessian_holder_four {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ H ≥ 0,
      ∀ N : E, ‖N‖=1 → ∀ V : Set E, (∀ x ∈ V, 0 ≤ inner ℝ N x) →
      ∀ (u : E → ℝ) (P : E → E → ℝ), (∀ x ∈ V, IsQuadraticPolynomial (P x)) →
      (∀ x ∈ V, ∀ n : ℕ, ∀ z : E, 0 ≤ inner ℝ N z → ‖z-x‖ ≤ R*r^n →
        |u z-P x z| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2) →
      ∀ x ∈ V, ∀ y ∈ V, ‖x-y‖ < R/4 →
        ‖realHessian (P x) x-realHessian (P y) y‖ ≤ H*‖x-y‖^beta := by
  obtain ⟨beta,hbeta,hbeta1,hdecay⟩ := actual_half_decay_exponent_two hr hr1
  let H := (256*C)*(2/(R*r))^beta*2^beta
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨beta,hbeta,hbeta1,H,hH,?_⟩
  intro N hN V hV u P hP herr x hx y hy hnear
  by_cases hxy : x=y
  · subst y
    have he : realHessian (P x) x-realHessian (P x) x=(0 : Bilin) := by
      ext v w
      change realHessian (P x) x v w-realHessian (P x) x v w=0
      ring
    rw [he,show ‖(0 : Bilin)‖=0 from norm_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨n,hn,hpow⟩ := actual_geometric_half_radius_holder_select_two hR hr hr1 hbeta.le hdecay
    (by positivity : 0 < 2*‖x-y‖) (by linarith : 2*‖x-y‖ < R/2)
  have hh := actual_halfspace_quadratic_hessian_comparison_four hN (hV x hx)
    (mul_pos hR (pow_pos hr n)) (by linarith : ‖x-y‖ ≤ R*r^n/4)
    (by positivity : 0 ≤ C*(1/2 : ℝ)^n) (hP x hx) (hP y hy) (herr x hx n) (herr y hy n)
  calc
    _ ≤ 256*(C*(1/2 : ℝ)^n) := hh
    _ = (256*C)*(1/2 : ℝ)^n := by ring
    _ ≤ (256*C)*((2/(R*r))^beta*(2*‖x-y‖)^beta) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = H*‖x-y‖^beta := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]; dsimp only [H]; ring

end PowerConvexity
