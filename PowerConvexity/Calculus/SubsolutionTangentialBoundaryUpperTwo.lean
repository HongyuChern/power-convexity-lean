import PowerConvexity.Calculus.StrictSubsolutionBoundaryComparisonTwo
import PowerConvexity.Calculus.ConvexDefiningCurvature

/-! # Actual tangent Hessian upper bounds supplied by a strict subsolution

The coefficient depends only on the chosen defining chart and the subsolution.
This does not bound the mixed or normal second derivatives, and does not claim
parameter-uniform control of those coefficients.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem strict_subsolution_defining_tangent_upper_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
    ∃ lam > 0, J.derivative x = lam • fderiv ℝ f x ∧
      lam*‖N‖^2 ≤ fderiv ℝ w x N ∧
      ∀ v : E, fderiv ℝ f x v = 0 →
        J.hessian x v v ≤ (fderiv ℝ w x N/‖N‖^2)*realHessian f x v v := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (hNf v).symm) hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hyU : x-r • N ∈ U := hball (mem_ball_self hR)
  have hcomp := strict_subsolution_inward_boundary_derivative_two hU hconv hK a b hw hu J
    hwp hwd hud (fun y hy => (hwb y hy).trans (hub y hy).symm) hx
    (x-r • N) (subset_closure hyU)
  rw [show x-r • N-x = -r • N by module,hJ] at hcomp
  simp only [map_smul,smul_apply,smul_eq_mul] at hcomp
  rw [hNN] at hcomp
  have hupper : lam*‖N‖^2 ≤ fderiv ℝ w x N := by nlinarith
  have hratio : lam ≤ fderiv ℝ w x N/‖N‖^2 :=
    (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hN))).mpr hupper
  refine ⟨lam,hlam,hJ,hupper,?_⟩
  intro v hv
  rw [hH v v hv hv]
  exact mul_le_mul_of_nonneg_right hratio
    (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv)

end PowerConvexity
