import PowerConvexity.Calculus.BoundaryZeroTangentHessian
import PowerConvexity.Calculus.QuadraticBallPotential

/-! # A regular zero boundary function on a sphere has no null real tangent -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ball_regular_zero_boundary_tangent_hessian_ne_zero
    {R : ℝ} (hR : 0 < R) {x v : E} (hx : ‖x‖ = R) (hv : v ≠ 0)
    (htan : inner ℝ x v = 0) {g : E → ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hDg : fderiv ℝ g x ≠ 0)
    (hgb : ∀ z ∈ frontier (ball (0 : E) R), g z = 0) :
    realHessian g x v v ≠ 0 := by
  let phi : E → ℝ := quadraticBallPotential 1 R
  have hphi : ContDiffAt ℝ 2 phi x := (quadraticBallPotential_contDiff 1 R 2).contDiffAt
  have hphix : phi x = 0 := by simp only [phi,quadraticBallPotential,hx,sub_self,mul_zero]
  have hdphi : HasFDerivAt phi (2 • innerSL ℝ x) x := by
    change HasFDerivAt (fun y : E => 1*(‖y‖^2-R^2)) _ x
    simpa only [one_mul] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (R^2)
  have hDphi : fderiv ℝ phi x ≠ 0 := by
    intro hz
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D x) hz
    rw [hdphi.fderiv] at hh
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,innerSL_apply_apply,smul_eq_mul,
      ContinuousLinearMap.zero_apply,real_inner_self_eq_norm_sq,hx,two_smul] at hh
    nlinarith [sq_pos_of_pos hR]
  have hdef : ∀ᶠ z in 𝓝 x, z ∈ ball (0 : E) R ↔ phi z < 0 := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [mem_ball,dist_zero_right,phi,quadraticBallPotential,one_mul,sub_neg]
    exact (sq_lt_sq₀ (norm_nonneg z) hR.le).symm
  obtain ⟨hD,hH⟩ := zero_boundary_function_defining_derivative_hessian
    isOpen_ball hphi hphix hDphi hdef hg hgb
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ phi x)
  let lam : ℝ := fderiv ℝ g x N/‖N‖^2
  have hlam : lam ≠ 0 := by
    intro hz
    apply hDg
    change fderiv ℝ g x = lam • fderiv ℝ phi x at hD
    rw [hD,hz,zero_smul]
  have hvphi : fderiv ℝ phi x v = 0 := by
    rw [hdphi.fderiv]
    simp only [ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul,htan,smul_zero]
  rw [hH v v hvphi hvphi,quadraticBallPotential_realHessian,real_inner_self_eq_norm_sq]
  change lam*(2*1*‖v‖^2) ≠ 0
  exact mul_ne_zero hlam (by have := norm_pos_iff.mpr hv; positivity)

end PowerConvexity
