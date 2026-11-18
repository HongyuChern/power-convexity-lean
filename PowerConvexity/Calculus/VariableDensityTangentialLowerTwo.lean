import PowerConvexity.Calculus.UniformComplexTangentialLowerTwo
import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo

/-! # A fixed positive complex-tangential margin for actual det>=1 solutions.
The comparison uses a genuinely small scaled potential. Convexity is used only
for nonnegative real curvature; strict positivity is paired complex positivity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem strictPsh_uniform_scaled_supersolution_comparison_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef) :
    ∃ c > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian a b u x).det.re) →
      (∀ x ∈ closure U, u x ≤ c*w x) ∧
      ∀ x ∈ frontier U, ∀ y ∈ closure U,
        J.derivative x (y-x) ≤ c*fderiv ℝ w x (y-x) := by
  obtain ⟨c,hc,hscale⟩ := compact_strictPsh_has_small_det_scaling_two a b hK hw hwp
  let W : E → ℝ := fun y => c*w y
  have hW : ContDiff ℝ 2 W := contDiff_const.mul hw
  have hWb : ∀ x ∈ frontier U, W x = 0 := fun x hx => by simp only [W,hwb x hx,mul_zero]
  refine ⟨c,hc,?_⟩
  intro u J hu hub hup hud
  have hle : ∀ x ∈ closure U, u x ≤ W x := by
    apply classical_strict_comparison_two hU hK a b J.continuous_value
      hW.continuous.continuousOn hu hW.contDiffOn hup
    · intro x hx
      exact lt_of_lt_of_le (hscale x (subset_closure hx)).2 (hud x hx)
    · intro x hx
      rw [hub x hx,hWb x hx]
  refine ⟨hle,?_⟩
  intro x hx y hy
  have hm : IsMinOn (fun z => W z-u z) (closure U) x := by
    intro z hz
    change W x-u x ≤ W z-u z
    rw [hWb x hx,hub x hx,sub_self]
    exact sub_nonneg.mpr (hle z hz)
  have hdu := closureJet_hasFDerivWithinAt hU hconv
    (hu.differentiableOn (by norm_num)) J (frontier_subset_closure hx)
  have hdW : HasFDerivWithinAt W (fderiv ℝ W x) (closure U) x :=
    (hW.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hh := hm.localize.hasFDerivWithinAt_nonneg (hdW.sub hdu)
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))
  have hder : fderiv ℝ W x = c • fderiv ℝ w x :=
    fderiv_const_mul (hw.contDiffAt.differentiableAt (by norm_num)) c
  rw [hder] at hh
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,sub_nonneg] using hh


theorem strictPsh_uniform_scaled_boundary_tangent_lower_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef) :
    ∃ c > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian a b u x).det.re) →
      ∀ x ∈ frontier U, ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
        fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) →
        ∀ v : E, fderiv ℝ f x v = 0 → c*realHessian w x v v ≤ J.hessian x v v := by
  obtain ⟨c,hc,hcomp⟩ := strictPsh_uniform_scaled_supersolution_comparison_of_det_lower_two
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
  obtain ⟨mu,hmu,hJu,hHu⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
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


theorem strictPsh_uniform_boundary_complex_tangent_lower_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef) :
    ∃ delta > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian e (fun j => Complex.I • e j) u x).det.re) →
      ∀ x ∈ frontier U, ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
        fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) →
        ∀ v : E, fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
          delta*‖v‖^2 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v) := by
  obtain ⟨c,hc,hscaled⟩ := strictPsh_uniform_scaled_boundary_tangent_lower_of_det_lower_two
    hU hconv hK e (fun j => Complex.I • e j) hab hw hwb hwp
  obtain ⟨eps,heps,hpaired⟩ := compact_strictPsh_paired_uniform_lower_two e hK hw hwp
  refine ⟨c*eps,mul_pos hc heps,?_⟩
  intro u J hu hub hup hud x hx f hf hfx hDf hdef v hv hIv
  have h1 := hscaled u J hu hub hup hud x hx f hf hfx hDf hdef v hv
  have h2 := hscaled u J hu hub hup hud x hx f hf hfx hDf hdef (Complex.I • v) hIv
  have h3 := mul_le_mul_of_nonneg_left (hpaired x (frontier_subset_closure hx) v) hc.le
  nlinarith only [h1,h2,h3]


end PowerConvexity
