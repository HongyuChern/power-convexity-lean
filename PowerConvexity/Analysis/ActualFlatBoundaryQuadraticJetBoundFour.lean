import PowerConvexity.Analysis.ActualHalfspaceQuadraticAbsoluteBoundFour
import PowerConvexity.Analysis.ActualFlatBoundaryJetFieldFour

/-! # Uniform absolute jets of the actual boundary quadratic field -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_quadratic_remainder_value_bound_four {N c : E}
    (hc : c ∈ actualFlatBoundaryDiskFour N) {R gamma M B : ℝ}
    (hR : 0 < R) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M) {u q : E → ℝ}
    (hu : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ B)
    (herr : ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ < R/2 →
      |u x-q x| ≤ M*‖x-c‖^2*‖x-c‖^gamma) :
    ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ min (R/4) (1/4 : ℝ) → |q x| ≤ B+M := by
  intro x hx hnear
  have hn4 : ‖x-c‖ ≤ (1/4 : ℝ) := hnear.trans (min_le_right _ _)
  have hnR : ‖x-c‖ < R/2 := (hnear.trans (min_le_left _ _)).trans_lt (by linarith)
  have hn1 : ‖x-c‖ ≤ 1 := hn4.trans (by norm_num)
  have hxU : x ∈ actualFlatClosedUpperBallFour N 1 := by
    refine ⟨?_,hx⟩
    rw [mem_closedBall,dist_zero_right]
    have hh := norm_le_insert' x c
    have hcN := hc.2
    linarith
  have hsq : ‖x-c‖^2 ≤ 1 := by nlinarith [norm_nonneg (x-c)]
  have hpw : ‖x-c‖^gamma ≤ 1 := Real.rpow_le_one (norm_nonneg _) hn1 hgamma
  have herror : |u x-q x| ≤ M := by
    calc
      _ ≤ M*‖x-c‖^2*‖x-c‖^gamma := herr x hx hnR
      _ ≤ M*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left hsq hM) hpw
        (Real.rpow_nonneg (norm_nonneg _) gamma) (by simpa only [mul_one] using hM)
      _ = M := by ring
  have he : q x=u x-(u x-q x) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (hu x hxU) herror)

theorem actual_flat_quadratic_remainder_jet_bound_four {R gamma M B : ℝ}
    (hR : 0 < R) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ T ≥ 0, ∀ N : E, ‖N‖=1 → ∀ c ∈ actualFlatBoundaryDiskFour N,
      ∀ u q : E → ℝ, IsQuadraticPolynomial q →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ B) →
      (∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ < R/2 →
        |u x-q x| ≤ M*‖x-c‖^2*‖x-c‖^gamma) →
      ‖fderiv ℝ q c‖ ≤ T ∧ ∀ x : E, ‖realHessian q x‖ ≤ T := by
  let r := min (R/4) (1/4 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  let T := max (68*(B+M)/r) (128*(B+M)/r^2)
  have hT : 0 ≤ T := (by positivity : 0 ≤ 68*(B+M)/r).trans (le_max_left _ _)
  refine ⟨T,hT,?_⟩
  intro N hN c hc u q hq hu herr
  have hb := actual_flat_quadratic_remainder_value_bound_four hc hR hgamma hM hu herr
  have hc0 : 0 ≤ inner ℝ N c := le_of_eq hc.1.symm
  refine ⟨(actual_halfspace_quadratic_absolute_gradient_four hN hc0 hr (add_nonneg hB hM) hq hb).trans
    (le_max_left _ _),?_⟩
  intro x
  exact (actual_halfspace_quadratic_absolute_hessian_four hN hc0 hr (add_nonneg hB hM) hq hb x).trans
    (le_max_right _ _)

end PowerConvexity
