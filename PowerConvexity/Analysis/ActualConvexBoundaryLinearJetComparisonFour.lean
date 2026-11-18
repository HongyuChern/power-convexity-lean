import PowerConvexity.Analysis.ActualConvexBoundaryGradientComparisonFour

/-! # Actual boundary derivative compatibility from common linear expansions

The two affine jets are compared on the genuine shared interior probe ball
of the convex domain. No boundary derivative modulus is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_centered_linear_isQuadratic_four (L : E →L[ℝ] ℝ) (c : E) :
    IsQuadraticPolynomial (fun x => L (x-c)) := by
  refine ⟨-L c,L,0,fun _ _ => rfl,?_⟩
  intro x
  simp only [map_sub,_root_.zero_apply,add_zero]
  ring

theorem actual_centered_linear_fderiv_four (L : E →L[ℝ] ℝ) (c x : E) :
    fderiv ℝ (fun y => L (y-c)) x=L := by
  have he : (fun y => L (y-c))=(fun y => L y-L c) := funext (fun y => map_sub L y c)
  rw [he,fderiv_sub_const,ContinuousLinearMap.fderiv]

theorem actual_centered_linear_hessian_four (L : E →L[ℝ] ℝ) (c x : E) :
    realHessian (fun y => L (y-c)) x=0 := by
  have he : fderiv ℝ (fun y => L (y-c))=(fun _ => L) :=
    funext (actual_centered_linear_fderiv_four L c)
  rw [realHessian,he]
  exact fderiv_const_apply _

theorem actual_convex_boundary_linear_derivative_holder_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {o : E} {rho D R M alpha : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hR : 0 < R) (hM : 0 ≤ M) (halpha : 0 ≤ alpha)
    (hball : closedBall o rho ⊆ U) {V : Set E} (hV : V ⊆ closure U)
    (hbound : ∀ c ∈ V, ‖o-c‖ ≤ D) {u : E → ℝ} {L : E → E →L[ℝ] ℝ}
    (herr : ∀ c ∈ V, ∀ x ∈ U, ‖x-c‖ < R →
      |u x-L c (x-c)| ≤ M*‖x-c‖*‖x-c‖^alpha) :
    ∀ c ∈ V, ∀ d ∈ V, ‖c-d‖ < min (R/4) (D+rho) →
      ‖L c-L d‖ ≤ (72*M*(4 : ℝ)^alpha*(D+rho)^2/rho^2)*‖c-d‖^alpha := by
  intro c hc d hd hnear
  by_cases hcd : c=d
  · subst d
    rw [sub_self,norm_zero,sub_self,norm_zero]
    positivity
  have hdpos : 0 < ‖c-d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcd)
  let s := 4*‖c-d‖
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : s < R := by have hh := hnear.trans_le (min_le_left _ _); dsimp [s]; linarith
  have hsD : s ≤ 4*(D+rho) := by have hh := hnear.trans_le (min_le_right _ _); dsimp [s]; linarith
  let C := M*s^alpha/s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have herror (e : E) (he : e ∈ V) (x : E) (hx : x ∈ U) (hxe : ‖x-e‖ ≤ s) :
      |u x-L e (x-e)| ≤ C*s^2 := by
    calc
      _ ≤ M*‖x-e‖*‖x-e‖^alpha := herr e he x hx (hxe.trans_lt hsR)
      _ ≤ M*s*s^alpha := mul_le_mul (mul_le_mul_of_nonneg_left hxe hM)
        (Real.rpow_le_rpow (norm_nonneg _) hxe halpha) (Real.rpow_nonneg (norm_nonneg _) alpha) (by positivity)
      _ = C*s^2 := by dsimp [C]; field_simp
  have hh := actual_convex_boundary_gradient_comparison_four hU hconv hrho hD hs hsD hC
    hball (hV hc) (hbound c hc) (by dsimp [s]; linarith : ‖c-d‖ ≤ s/4)
    (actual_centered_linear_isQuadratic_four (L c) c)
    (actual_centered_linear_isQuadratic_four (L d) d)
    (show ‖realHessian (fun x => L d (x-d)) 0‖ ≤ (0 : ℝ) by
      rw [actual_centered_linear_hessian_four]
      exact le_of_eq (ContinuousLinearMap.opNorm_zero))
    (herror c hc) (herror d hd)
  rw [actual_centered_linear_fderiv_four,actual_centered_linear_fderiv_four,zero_mul,add_zero] at hh
  have hsalpha : s^alpha=(4 : ℝ)^alpha*‖c-d‖^alpha := by
    exact Real.mul_rpow (by norm_num) (norm_nonneg _)
  have he : (72*C*(D+rho)^2/rho^2)*s=
      (72*M*(4 : ℝ)^alpha*(D+rho)^2/rho^2)*‖c-d‖^alpha := by
    dsimp only [C]
    rw [hsalpha]
    field_simp
  exact hh.trans_eq he

end PowerConvexity
