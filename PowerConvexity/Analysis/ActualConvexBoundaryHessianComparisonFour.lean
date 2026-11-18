import PowerConvexity.Analysis.ActualConvexBoundaryProbeFour

/-! # Actual boundary Hessian comparison from an interior probe in a convex domain -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_convex_boundary_hessian_comparison_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o c d : E} {rho D s C : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hs : 0 < s) (hsD : s ≤ 4*(D+rho)) (hC : 0 ≤ C)
    (hball : closedBall o rho ⊆ U) (hc : c ∈ closure U)
    (hco : ‖o-c‖ ≤ D) (hcd : ‖c-d‖ ≤ s/4) {u p q : E → ℝ}
    (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q)
    (hpE : ∀ z ∈ U, ‖z-c‖ ≤ s → |u z-p z| ≤ C*s^2)
    (hqE : ∀ z ∈ U, ‖z-d‖ ≤ s → |u z-q z| ≤ C*s^2) :
    ‖realHessian p c-realHessian q d‖ ≤ 256*C*(D+rho)^2/rho^2 := by
  let theta := s/(4*(D+rho))
  let a := c+theta • (o-c)
  let r := theta*rho
  let K := 32*C*(D+rho)^2/rho^2
  have hDrho : 0 < D+rho := by positivity
  have hr : 0 < r := by dsimp [r,theta]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hscale : K*r^2=2*C*s^2 := by
    dsimp [K,r,theta]
    field_simp
    <;> ring
  have hd := IsQuadraticPolynomial_sub hp hq
  have hsup : ∀ w ∈ closedBall (0 : E) r, |p (a+w)-q (a+w)| ≤ K*r^2 := by
    intro w hw
    obtain ⟨hz,hzc,hzd⟩ := actual_convex_boundary_shared_probe_four
      hU hconv hrho hD hs hsD hball hc hco hcd w hw
    have hh := abs_sub_le (p (a+w)) (u (a+w)) (q (a+w))
    rw [abs_sub_comm (p (a+w)) (u (a+w))] at hh
    exact (hh.trans (add_le_add (hpE _ hz hzc) (hqE _ hz hzd))).trans_eq (by rw [hscale]; ring)
  have hh := (actual_quadratic_scaled_sup_jets_at_four hd a hr hK hsup).2.2
  have he : realHessian (fun z => p z-q z) a=realHessian p c-realHessian q d := by
    rw [realHessian_sub_at (IsQuadraticPolynomial_contDiff hp 2).contDiffAt
      (IsQuadraticPolynomial_contDiff hq 2).contDiffAt]
    rw [quadratic_realHessian_from_jet_zero hp a,quadratic_realHessian_from_jet_zero hp c,
      quadratic_realHessian_from_jet_zero hq a,quadratic_realHessian_from_jet_zero hq d]
  rw [he] at hh
  exact hh.trans_eq (by dsimp [K]; ring)

theorem actual_convex_boundary_hessian_holder_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o : E} {rho D R M beta : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hR : 0 < R) (hM : 0 ≤ M) (hbeta : 0 ≤ beta)
    (hball : closedBall o rho ⊆ U) {V : Set E} (hV : V ⊆ closure U)
    (hbound : ∀ c ∈ V, ‖o-c‖ ≤ D) {u : E → ℝ} {P : E → E → ℝ}
    (hP : ∀ c ∈ V, IsQuadraticPolynomial (P c))
    (herr : ∀ c ∈ V, ∀ z ∈ U, ‖z-c‖ < R →
      |u z-P c z| ≤ M*‖z-c‖^2*‖z-c‖^beta) :
    ∀ c ∈ V, ∀ d ∈ V, ‖c-d‖ < min (R/4) (D+rho) →
      ‖realHessian (P c) c-realHessian (P d) d‖ ≤
        (256*M*(D+rho)^2/rho^2*(4 : ℝ)^beta)*‖c-d‖^beta := by
  intro c hc d hd hnear
  by_cases hcd0 : c=d
  · subst d
    have he : realHessian (P c) c-realHessian (P c) c=(0 : E →L[ℝ] E →L[ℝ] ℝ) := by
      ext v w
      change realHessian (P c) c v w-realHessian (P c) c v w=0
      ring
    rw [he,show ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖=0 from norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) beta)
  have hdist : 0 < ‖c-d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcd0)
  let s := 4*‖c-d‖
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : s < R := by have hh := hnear.trans_le (min_le_left _ _); dsimp [s]; linarith
  have hsD : s ≤ 4*(D+rho) := by have hh := hnear.trans_le (min_le_right _ _); dsimp [s]; linarith
  have herror (e : E) (he : e ∈ V) (z : E) (hz : z ∈ U) (hze : ‖z-e‖ ≤ s) :
      |u z-P e z| ≤ (M*s^beta)*s^2 := by
    calc
      _ ≤ M*‖z-e‖^2*‖z-e‖^beta := herr e he z hz (hze.trans_lt hsR)
      _ ≤ M*s^2*s^beta := by gcongr
      _ = _ := by ring
  have hh := actual_convex_boundary_hessian_comparison_four hU hconv hrho hD hs hsD
    (by positivity : 0 ≤ M*s^beta) hball (hV hc) (hbound c hc)
    (by dsimp [s]; linarith : ‖c-d‖ ≤ s/4) (hP c hc) (hP d hd) (herror c hc) (herror d hd)
  apply hh.trans_eq
  dsimp [s]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)]
  ring

end PowerConvexity
