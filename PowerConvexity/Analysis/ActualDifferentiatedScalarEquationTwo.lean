import PowerConvexity.Analysis.ActualCofactorFirstVariationTwo
import PowerConvexity.Calculus.ActualHigherDerivativeIdentitiesTwo

/-! # Differentiating the actual non-divergence equation

The derivative of the coefficient is retained as a genuine source term.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_differentiate_scalar_equation_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat} {p f : E → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun y => a y i j) U)
    (hp : ContDiffOn ℝ 3 p U)
    (heq : ∀ y ∈ U, (∑ i, ∑ j, a y i j*euclideanHessian p y i j) = f y)
    {x : E} (hx : x ∈ U) (v : E) :
    (∑ i, ∑ j, a x i j*euclideanHessian (fun y => fderiv ℝ p y v) x i j) =
      fderiv ℝ f x v-
        ∑ i, ∑ j, fderiv ℝ (fun y => a y i j) x v*euclideanHessian p x i j := by
  have hp3 := hp.contDiffAt (hU.mem_nhds hx)
  have hH : ContDiffAt ℝ 1 (realHessian p) x :=
    (hp3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have haD (i j : Fin (2+2)) := ((ha i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hHD (i j : Fin (2+2)) : DifferentiableAt ℝ (fun y => euclideanHessian p y i j) x :=
    ((hH.clm_apply contDiffAt_const).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (haD i j).hasFDerivAt.mul (hHD i j).hasFDerivAt))
  have he : (fun y => ∑ i, ∑ j, a y i j*euclideanHessian p y i j) =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L v) (hsum.fderiv.symm.trans (he.fderiv_eq (𝕜 := ℝ)))
  simp only [_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hd
  have hentry (i j : Fin (2+2)) :
      fderiv ℝ (fun y => euclideanHessian p y i j) x v =
        euclideanHessian (fun y => fderiv ℝ p y v) x i j :=
    actual_Hessian_directional_differentiation_two hp3 v (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp_rw [hentry] at hd
  simp only [Finset.sum_add_distrib] at hd
  have hprod : (∑ i, ∑ j, euclideanHessian p x i j*fderiv ℝ (fun y => a y i j) x v) =
      ∑ i, ∑ j, fderiv ℝ (fun y => a y i j) x v*euclideanHessian p x i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprod] at hd
  linarith

end PowerConvexity
