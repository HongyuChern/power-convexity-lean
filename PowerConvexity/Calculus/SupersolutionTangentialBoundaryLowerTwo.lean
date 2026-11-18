import PowerConvexity.Calculus.SmallScaledSupersolutionTwo
import PowerConvexity.Calculus.BoundaryZeroTangentHessian
import PowerConvexity.Calculus.ConvexDefiningCurvature

/-! # A common lower tangent Hessian comparison with a scaled fixed potential

Convexity gives nonnegative real second fundamental form. The small actual
supersolution controls the normal derivative and hence every actual tangent
quadratic Hessian value. No uniform interior-ball radius is needed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem strictPsh_uniform_scaled_boundary_tangent_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef) :
    ∃ c > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (complexHessian a b u x).det = 1) →
      ∀ x ∈ frontier U, ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
        fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) →
        ∀ v : E, fderiv ℝ f x v = 0 → c*realHessian w x v v ≤ J.hessian x v v := by
  obtain ⟨c,hc,hcomp⟩ := strictPsh_uniform_scaled_supersolution_comparison_two
    hU hconv hK a b hw hwb hwp
  refine ⟨c,hc,?_⟩
  intro u J hu hub hup hud x hx f hf hfx hDf hdef v hv
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (z : E) : inner ℝ N z = fderiv ℝ f x z := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext z
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hn : 0 < ‖N‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hN)
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨mu,hmu,hJu,hHu⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  obtain ⟨hDw,hHw⟩ := zero_boundary_function_defining_derivative_hessian
    hU hf hfx hDf hdef hw.contDiffAt hwb
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun z => (hNf z).symm) hdef
  have hy : x-r • N ∈ closure U := subset_closure (hball
    (mem_ball_self (mul_pos hr (norm_pos_iff.mpr hN))))
  have hh := (hcomp u J hu hub hup hud).2 x hx (x-r • N) hy
  rw [show x-r • N-x = -r • N by module,hJu] at hh
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,hNN] at hh
  have hnormal : c*fderiv ℝ w x N ≤ mu*‖N‖^2 := by nlinarith only [hh,hr]
  have hratio : c*(fderiv ℝ w x N/‖N‖^2) ≤ mu := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hn).mpr hnormal
  have hcurv := definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv
  rw [hHu v v hv hv,hHw v v hv hv]
  change c*((fderiv ℝ w x N/‖N‖^2)*realHessian f x v v) ≤ mu*realHessian f x v v
  have ht := mul_le_mul_of_nonneg_right hratio hcurv
  nlinarith only [ht]

end PowerConvexity
