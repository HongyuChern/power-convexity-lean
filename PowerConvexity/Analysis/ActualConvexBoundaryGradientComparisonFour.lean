import PowerConvexity.Analysis.ActualConvexBoundaryHessianComparisonFour
import PowerConvexity.Analysis.ActualFlatBoundaryGradientCompatibilityFour

/-! # First-jet compatibility on a convex boundary from the same genuine probe ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_convex_boundary_gradient_comparison_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o c d : E} {rho D s C T : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hs : 0 < s) (hsD : s ≤ 4*(D+rho)) (hC : 0 ≤ C)
    (hball : closedBall o rho ⊆ U) (hc : c ∈ closure U)
    (hco : ‖o-c‖ ≤ D) (hcd : ‖c-d‖ ≤ s/4) {u p q : E → ℝ}
    (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q) (hqT : ‖realHessian q 0‖ ≤ T)
    (hpE : ∀ z ∈ U, ‖z-c‖ ≤ s → |u z-p z| ≤ C*s^2)
    (hqE : ∀ z ∈ U, ‖z-d‖ ≤ s → |u z-q z| ≤ C*s^2) :
    ‖fderiv ℝ p c-fderiv ℝ q d‖ ≤ (72*C*(D+rho)^2/rho^2)*s+T*‖c-d‖ := by
  let theta := s/(4*(D+rho))
  let a := c+theta • (o-c)
  let r := theta*rho
  let K := 32*C*(D+rho)^2/rho^2
  have hDrho : 0 < D+rho := by positivity
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hr : 0 < r := mul_pos ht hrho
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htotal : theta*(D+rho)=s/4 := by dsimp [theta]; field_simp
  have hrs : r ≤ s/4 := by
    have hh := mul_le_mul_of_nonneg_left (show rho ≤ D+rho by linarith) ht.le
    simpa only [htotal,r] using hh
  have hca : ‖c-a‖ ≤ s/4 := by
    have he : c-a=-(theta • (o-c)) := by dsimp [a]; abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hco ht.le).trans
      (by have hh := mul_nonneg ht.le hrho.le; linarith [htotal])
  have hd := IsQuadraticPolynomial_sub hp hq
  have hscale : K*r^2=2*C*s^2 := by dsimp [K,r,theta]; field_simp <;> ring
  have hsup : ∀ w ∈ closedBall (0 : E) r, |p (a+w)-q (a+w)| ≤ K*r^2 := by
    intro w hw
    obtain ⟨hz,hzc,hzd⟩ := actual_convex_boundary_shared_probe_four hU hconv hrho hD hs hsD hball hc hco hcd w hw
    have hh := abs_sub_le (p (a+w)) (u (a+w)) (q (a+w))
    rw [abs_sub_comm (p (a+w)) (u (a+w))] at hh
    exact (hh.trans (add_le_add (hpE _ hz hzc) (hqE _ hz hzd))).trans_eq (by rw [hscale]; ring)
  have hjet := actual_quadratic_scaled_sup_jets_at_four hd a hr hK hsup
  have hHd : ‖realHessian (fun z => p z-q z) 0‖ ≤ 8*K := by
    simpa only [quadratic_realHessian_from_jet_zero hd a] using hjet.2.2
  have hmove := actual_quadratic_gradient_difference_bound_four hd hHd c a
  have hdc : ‖fderiv ℝ (fun z => p z-q z) c‖ ≤ (72*C*(D+rho)^2/rho^2)*s := by
    apply (norm_le_insert' (fderiv ℝ (fun z => p z-q z) c) (fderiv ℝ (fun z => p z-q z) a)).trans
    apply (add_le_add hjet.2.1 hmove).trans
    calc
      K*r+8*K*‖c-a‖ ≤ K*(s/4)+8*K*(s/4) :=
        add_le_add (mul_le_mul_of_nonneg_left hrs hK) (mul_le_mul_of_nonneg_left hca (by positivity))
      _ = _ := by dsimp [K]; ring
  have heD : fderiv ℝ (fun z => p z-q z) c=fderiv ℝ p c-fderiv ℝ q c :=
    fderiv_fun_sub ((IsQuadraticPolynomial_contDiff hp 1).contDiffAt.differentiableAt (by norm_num))
      ((IsQuadraticPolynomial_contDiff hq 1).contDiffAt.differentiableAt (by norm_num))
  rw [heD] at hdc
  have hh : ‖fderiv ℝ p c-fderiv ℝ q d‖ ≤
      ‖fderiv ℝ p c-fderiv ℝ q c‖+‖fderiv ℝ q c-fderiv ℝ q d‖ := by
    simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ p c) (fderiv ℝ q c) (fderiv ℝ q d)
  exact hh.trans (add_le_add hdc (actual_quadratic_gradient_difference_bound_four hq hqT c d))

theorem actual_convex_boundary_gradient_lipschitz_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o : E} {rho D R M T beta : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hR : 0 < R) (hM : 0 ≤ M) (hbeta : 0 ≤ beta)
    (hball : closedBall o rho ⊆ U) {V : Set E} (hV : V ⊆ closure U)
    (hbound : ∀ c ∈ V, ‖o-c‖ ≤ D) {u : E → ℝ} {P : E → E → ℝ}
    (hP : ∀ c ∈ V, IsQuadraticPolynomial (P c)) (hT : ∀ c ∈ V, ‖realHessian (P c) 0‖ ≤ T)
    (herr : ∀ c ∈ V, ∀ z ∈ U, ‖z-c‖ < R → |u z-P c z| ≤ M*‖z-c‖^2*‖z-c‖^beta) :
    ∀ c ∈ V, ∀ d ∈ V, ‖c-d‖ < min (R/4) (min (D+rho) (1/4 : ℝ)) →
      ‖fderiv ℝ (P c) c-fderiv ℝ (P d) d‖ ≤ (288*M*(D+rho)^2/rho^2+T)*‖c-d‖ := by
  intro c hc d hd hnear
  by_cases hcd0 : c=d
  · subst d
    have he : fderiv ℝ (P c) c-fderiv ℝ (P c) c=(0 : E →L[ℝ] ℝ) := sub_self _
    rw [he,show ‖(0 : E →L[ℝ] ℝ)‖=0 from norm_zero,sub_self,norm_zero,mul_zero]
  have hdist : 0 < ‖c-d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcd0)
  let s := 4*‖c-d‖
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : s < R := by have hh := hnear.trans_le (min_le_left _ _); dsimp [s]; linarith
  have hsD : s ≤ 4*(D+rho) := by
    have hh := hnear.trans_le ((min_le_right _ _).trans (min_le_left _ _)); dsimp [s]; linarith
  have hs1 : s ≤ 1 := by
    have hh := hnear.trans_le ((min_le_right _ _).trans (min_le_right _ _)); dsimp [s]; linarith
  have hpw : s^beta ≤ 1 := Real.rpow_le_one hs.le hs1 hbeta
  have herror (e : E) (he : e ∈ V) (z : E) (hz : z ∈ U) (hze : ‖z-e‖ ≤ s) :
      |u z-P e z| ≤ M*s^2 := by
    calc
      _ ≤ M*‖z-e‖^2*‖z-e‖^beta := herr e he z hz (hze.trans_lt hsR)
      _ ≤ M*s^2*s^beta := by gcongr
      _ ≤ M*s^2*1 := mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = _ := mul_one _
  have hh := actual_convex_boundary_gradient_comparison_four hU hconv hrho hD hs hsD hM
    hball (hV hc) (hbound c hc) (by dsimp [s]; linarith : ‖c-d‖ ≤ s/4)
    (hP c hc) (hP d hd) (hT d hd) (herror c hc) (herror d hd)
  exact hh.trans_eq (by dsimp [s]; ring)

end PowerConvexity
