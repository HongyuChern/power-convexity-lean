import PowerConvexity.Analysis.ActualPhysicalQuadraticTwo

/-! # Genuine original-coordinate bounds for the boundary quadratic -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_affine_hessian_norm_bound_four
    (T : E →L[ℝ] E) (c x : E) {q : E → ℝ} {H L : ℝ}
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hq : ContDiffAt ℝ 2 q (c+T x))
    (hqH : ‖realHessian q (c+T x)‖ ≤ H) (hT : ‖T‖ ≤ L) :
    ‖realHessian (fun y => q (c+T y)) x‖ ≤ H*L^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [realHessian_comp_affine T c hq]
  have hv : ‖T v‖ ≤ L*‖v‖ := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hw : ‖T w‖ ≤ L*‖w‖ := (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg w))
  exact ((realHessian q (c+T x)).le_opNorm₂ (T v) (T w)).trans
    ((mul_le_mul (mul_le_mul hqH hv (norm_nonneg _) hH) hw (norm_nonneg _) (by positivity)).trans_eq (by ring))

theorem actual_physical_boundary_quadratic_bounds_four
    (G : E ≃L[ℝ] E) (c : E) {r I G₀ H₀ : ℝ}
    (hr : 0 < r) (hI : 0 ≤ I) (hG₀ : 0 ≤ G₀) (hH₀ : 0 ≤ H₀)
    (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p)
    (hpG : ‖fderiv ℝ p 0‖ ≤ G₀) (hpH : ∀ x, ‖realHessian p x‖ ≤ H₀) :
    let P := actualPhysicalQuadraticTwo G (G.symm c) r p
    ‖fderiv ℝ P c‖ ≤ G₀*(I/r) ∧ ∀ x, ‖realHessian P x‖ ≤ H₀*(I/r)^2 := by
  let T : E →L[ℝ] E := r⁻¹ • G.symm.toContinuousLinearMap
  let b : E := -(r⁻¹ • G.symm c)
  have hT : ‖T‖ ≤ I/r := by
    change ‖r⁻¹ • G.symm.toContinuousLinearMap‖ ≤ I/r
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left hInv (inv_pos.mpr hr).le).trans_eq (by ring)
  have hcenter : b+T c=0 := by simp only [b,T,ContinuousLinearMap.smul_apply,ContinuousLinearEquiv.coe_coe,neg_add_cancel]
  have he : actualPhysicalQuadraticTwo G (G.symm c) r p=(fun x => p (b+T x)) := by
    funext x
    simp only [actualPhysicalQuadraticTwo,b,T,ContinuousLinearMap.smul_apply,
      ContinuousLinearEquiv.coe_coe,smul_sub]
    congr 1
    abel
  have hpc : ContDiffAt ℝ 2 p (b+T c) := (IsQuadraticPolynomial_contDiff hp 2).contDiffAt
  have hd := (hpc.differentiableAt (by norm_num)).hasFDerivAt.comp c (T.hasFDerivAt.const_add b)
  constructor
  · rw [he]
    change ‖fderiv ℝ (p ∘ fun x => b+T x) c‖ ≤ G₀*(I/r)
    rw [hd.fderiv,hcenter]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hpG hT (norm_nonneg _) hG₀)
  · intro x
    rw [he]
    exact actual_affine_hessian_norm_bound_four T b x hH₀ (div_nonneg hI hr.le)
      (IsQuadraticPolynomial_contDiff hp 2).contDiffAt (hpH _) hT

end PowerConvexity
