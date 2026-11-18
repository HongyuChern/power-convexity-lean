import PowerConvexity.Calculus.SupersolutionTangentialBoundaryLowerTwo
import PowerConvexity.Calculus.UniformStrictPshMarginTwo

/-! # A uniform positive complex-tangential boundary margin

The actual fixed strict psh potential has a compact paired-Hessian margin.
Scaling it into a genuine supersolution transfers that margin to every actual
classical solution, uniformly on the boundary and in all complex tangents.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem compact_strictPsh_paired_uniform_lower_two
    (e : Module.Basis (Fin 2) ℂ E)
    {S : Set E} (hS : IsCompact S) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ S, (complexHessian e (fun j => Complex.I • e j) w x).PosDef) :
    ∃ delta > 0, ∀ x ∈ S, ∀ v : E,
      delta*‖v‖^2 ≤ realHessian w x v v+realHessian w x (Complex.I • v) (Complex.I • v) := by
  letI : FiniteDimensional ℂ E := e.finiteDimensional_of_finite
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  let Q := fun x => pairedBilinearForm I (realHessian w x)
  let N := pairedBilinearForm I (realHessian (fun y : E => ‖y‖^2) 0)
  have hHc : Continuous (realHessian w) := continuous_iff_continuousAt.mpr (fun _ =>
    ((hw.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hQc : Continuous Q := (continuous_pairedBilinearForm I).comp hHc
  have hQpos (x : E) (hx : x ∈ S) (v : E) (hv : v ≠ 0) : 0 < Q x v v := by
    simpa only [Q,pairedBilinearForm_apply,hI] using
      complexHessian_posDef_paired_positive_two e hw.contDiffAt (hwp x hx) v hv
  obtain ⟨eps,heps,hmargin⟩ := compact_positive_bilinear_subtraction_margin hS Q hQc N hQpos
  have hNv (v : E) : N v v = 4*‖v‖^2 := by
    simp only [N,pairedBilinearForm_apply,realHessian_norm_square,hI,
      real_inner_self_eq_norm_sq,norm_smul,Complex.norm_I,one_mul]
    ring
  refine ⟨4*eps,by positivity,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp only [norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,
      map_zero,smul_zero,add_zero,le_refl]
  · have hh := hmargin x hx v hv
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at hh
    rw [hNv] at hh
    change 0 < (realHessian w x v v+realHessian w x (Complex.I • v) (Complex.I • v))-eps*(4*‖v‖^2) at hh
    nlinarith only [hh]

theorem strictPsh_uniform_boundary_complex_tangent_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef) :
    ∃ delta > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) →
      ∀ x ∈ frontier U, ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
        fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) →
        ∀ v : E, fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
          delta*‖v‖^2 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v) := by
  obtain ⟨c,hc,hscaled⟩ := strictPsh_uniform_scaled_boundary_tangent_lower_two
    hU hconv hK e (fun j => Complex.I • e j) hab hw hwb hwp
  obtain ⟨eps,heps,hpaired⟩ := compact_strictPsh_paired_uniform_lower_two e hK hw hwp
  refine ⟨c*eps,mul_pos hc heps,?_⟩
  intro u J hu hub hup hud x hx f hf hfx hDf hdef v hv hIv
  have h1 := hscaled u J hu hub hup hud x hx f hf hfx hDf hdef v hv
  have h2 := hscaled u J hu hub hup hud x hx f hf hfx hDf hdef (Complex.I • v) hIv
  have h3 := mul_le_mul_of_nonneg_left (hpaired x (frontier_subset_closure hx) v) hc.le
  nlinarith only [h1,h2,h3]

end PowerConvexity
