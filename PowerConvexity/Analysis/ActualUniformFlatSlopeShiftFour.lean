import PowerConvexity.Analysis.ActualUniformFlatPositivePropagationFour

/-! # Exact source terms after subtracting a boundary slope

The normal affine terms have zero actual Hessian. Their drift contribution is
retained in the real equation and bounded explicitly, rather than discarded.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_normal_linear_hessian_four (N : E) (c : ℝ) (x : E) :
    realHessian (fun y => c*inner ℝ N y) x=0 := by
  have he : fderiv ℝ (fun y => c*inner ℝ N y)=fun _ => c • innerSL ℝ N := by
    funext y
    exact (((innerSL ℝ N).hasFDerivAt (x := y)).const_smul c).fderiv
  unfold realHessian
  rw [he]
  simp

theorem actual_normal_affine_response_equation_four
    (N : E) (sigma c : ℝ) (A : Mat) (b : E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) {f : ℝ}
    (heq : (∑ i, ∑ j, A i j*euclideanHessian u x i j)+fderiv ℝ u x b = -f) :
    (∑ i, ∑ j, A i j*euclideanHessian
      (fun y => sigma*u y+c*inner ℝ N y) x i j)+
      fderiv ℝ (fun y => sigma*u y+c*inner ℝ N y) x b =
        -(sigma*f-c*inner ℝ N b) := by
  have hl : ContDiff ℝ 2 (fun y : E => c*inner ℝ N y) :=
    contDiff_const.mul (innerSL ℝ N).contDiff
  have hv : ContDiffAt ℝ 2 (fun y => sigma*u y+c*inner ℝ N y) x :=
    (contDiffAt_const.mul hu).add hl.contDiffAt
  have hH : realHessian (fun y => sigma*u y+c*inner ℝ N y) x=sigma • realHessian u x := by
    rw [realHessian_add (contDiffAt_const.mul hu) hl.contDiffAt,
      realHessian_const_mul,actual_normal_linear_hessian_four]
    ext v w
    simp only [_root_.add_apply,ContinuousLinearMap.zero_apply,add_zero]
  have hD := ((((hu.differentiableAt (by norm_num)).hasFDerivAt).const_smul sigma).add
    (((innerSL ℝ N).hasFDerivAt (x := x)).const_smul c)).fderiv
  change fderiv ℝ (fun y => sigma*u y+c*inner ℝ N y) x=
    sigma • fderiv ℝ u x+c • innerSL ℝ N at hD
  rw [← actual_matrix_contraction_euclideanHessian_four A hv,hH,map_smul,smul_eq_mul,
    actual_matrix_contraction_euclideanHessian_four A hu,hD,_root_.add_apply,_root_.smul_apply,_root_.smul_apply]
  change sigma*(∑ i, ∑ j, A i j*euclideanHessian u x i j)+
    (sigma*fderiv ℝ u x b+c*inner ℝ N b)=_
  calc
    _ = sigma*((∑ i, ∑ j, A i j*euclideanHessian u x i j)+fderiv ℝ u x b)+c*inner ℝ N b := by ring
    _ = _ := by rw [heq]; ring

theorem actual_normal_affine_source_bound_four {N : E} (hN : ‖N‖=1)
    {sigma c f F B S : ℝ} {b : E}
    (hsigma : |sigma| ≤ 1) (hc : |c| ≤ S) (hf : |f| ≤ F) (hb : ‖b‖ ≤ B) :
    |sigma*f-c*inner ℝ N b| ≤ F+B*S := by
  have hF : 0 ≤ F := (abs_nonneg f).trans hf
  have hS : 0 ≤ S := (abs_nonneg c).trans hc
  have hB : 0 ≤ B := (norm_nonneg b).trans hb
  have hn : |inner ℝ N b| ≤ B := by
    have hh := abs_real_inner_le_norm N b
    rw [hN,one_mul] at hh
    exact hh.trans hb
  calc
    _ ≤ |sigma*f|+|c*inner ℝ N b| := abs_sub _ _
    _ = |sigma| * |f|+|c| * |inner ℝ N b| := by rw [abs_mul,abs_mul]
    _ ≤ 1*F+S*B := add_le_add
      (mul_le_mul hsigma hf (abs_nonneg _) (by norm_num))
      (mul_le_mul hc hn (abs_nonneg _) hS)
    _ = _ := by ring

end PowerConvexity
