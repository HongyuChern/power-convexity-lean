import PowerConvexity.Analysis.ActualGraphShearCoefficientFour

/-! # Coordinate identities used by the actual graph-chart divergence -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_coordinate_sum_four (v : E) :
    (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
  ext j
  simp [Pi.single_apply]

theorem actual_shear_inverse_column_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0)
    (j : Fin (2+2)) :
    (∑ i, actualShearInverseMatrixFour N l i j •
      actualShearLinearEquivFour N l hl (EuclideanSpace.single i 1)) = EuclideanSpace.single j 1 := by
  rw [actual_shear_inverse_matrix_four N l hl]
  exact actual_linear_inverse_column_recovery_two _ j

theorem actual_shear_tangential_bilinear_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0)
    (H : Bilin) (hH : ∀ v w, H v w = H w v) (hN : ∀ v, H v N = 0) (v w : E) :
    H (actualShearLinearEquivFour N l hl v) (actualShearLinearEquivFour N l hl w) = H v w := by
  have hNv (z : E) : H N z=0 := (hH N z).trans (hN z)
  simp only [actual_shear_linear_apply_four,map_add,map_smul,_root_.add_apply,_root_.smul_apply,
    hN,hNv,smul_eq_mul,mul_zero,zero_add,add_zero]

theorem actual_shear_tangential_contraction_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0)
    (A : Mat) (H : Bilin) (hH : ∀ v w, H v w = H w v) (hN : ∀ v, H v N = 0) :
    (∑ i, ∑ j, (actualShearInverseMatrixFour N l*A*(actualShearInverseMatrixFour N l)ᵀ) i j *
      H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      ∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hh := actual_bilinear_congruence_contraction_four (actualShearLinearEquivFour N l hl) A H hH
  simp only [actual_shear_tangential_bilinear_four N l hl H hH hN] at hh
  simpa only [actualLinearCongruenceMatrixTwo,← actual_shear_inverse_matrix_four N l hl] using hh

theorem actual_normal_hessian_vanishes_four {rho : E → ℝ} {N x : E}
    (hrho : ContDiffAt ℝ 2 rho x)
    (hN : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N = 0) (v : E) : realHessian rho x v N = 0 := by
  have hd := ((hrho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const N x)
  have heq : (fun y => fderiv ℝ rho y N) =ᶠ[𝓝 x] (fun _ => 0) := hN
  have hzero := (heq.fderiv_eq (𝕜 := ℝ)).trans (hasFDerivAt_const (0 : ℝ) x).fderiv
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.fderiv.symm.trans hzero)
  simpa only [realHessian,ContinuousLinearMap.comp_zero,_root_.add_apply,
    ContinuousLinearMap.zero_apply,zero_add,ContinuousLinearMap.flip_apply] using hv

end PowerConvexity
