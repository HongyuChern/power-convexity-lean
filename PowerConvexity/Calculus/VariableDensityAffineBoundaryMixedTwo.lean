import PowerConvexity.Calculus.AffineBoundaryMixedJetTwo
import PowerConvexity.Calculus.VariableDensityAffineFieldTwo
import PowerConvexity.Calculus.InhomogeneousTraceBarrierTwo

/-! # Actual mixed closure jets from the affine field with retained density source -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem closure_affine_jet_abs_le_trace_barrier_with_source_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u V density : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (J : ClosureC2Jet u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hden : ContDiffOn ℝ 1 density U)
    (hud : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = (density x : ℂ))
    (hdenne : ∀ x ∈ U, density x ≠ 0)
    (K : E →L[ℂ] E) (c : E) (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hsource : ∀ x ∈ U, |fderiv ℝ density x (c+K x)/density x| ≤ A)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    (hVL : ∀ x ∈ U, complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹ (realHessian V x) ≤
      -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, |J.derivative x (c+K x)| ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, |J.derivative x (c+K x)| ≤ 2*(A+B)*V x+B*‖x-p‖^2 := by
  let g : E → ℝ := fun y => J.derivative y (c+K y)
  have heq (x : E) (hx : x ∈ U) : g =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (c+K y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact congrArg (fun D : E →L[ℝ] ℝ => D (c+K y)) (J.derivative_eq hy)
  have hgc : ContinuousOn g (closure U) := J.continuous_derivative.clm_apply
    (continuousOn_const.add K.continuous.continuousOn)
  have hg : ContDiffOn ℝ 2 g U := by
    intro x hx
    have hh : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K y)) x :=
      ((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 2) (by norm_num)).clm_apply
        (contDiffAt_const.add (K.restrictScalars ℝ).contDiff.contDiffAt)
    exact (hh.congr_of_eventuallyEq (heq x hx)).contDiffWithinAt
  have hgL (x : E) (hx : x ∈ U) :
      |linearizedCMAOperatorTwo e (fun j => Complex.I • e j) u g x| ≤ A := by
    have heH : realHessian g x = realHessian (fun y => fderiv ℝ u y (c+K y)) x :=
      (heq x hx).fderiv.fderiv_eq
    dsimp only [linearizedCMAOperatorTwo]
    rw [heH]
    have hh := complex_affine_field_variable_density_two e K c htrace hU hu hden hud hdenne hx
    change |linearizedCMAOperatorTwo e (fun j => Complex.I • e j) u
      (fun y => fderiv ℝ u y (c+K y)) x| ≤ A
    rw [hh]
    exact hsource x hx
  exact linearized_function_abs_le_trace_barrier_with_source_two hU hK e (fun j => Complex.I • e j) hab
    J.continuous_value (hu.of_le (by norm_num)) hub hup hgc hg hVc hV hVb hA hgL hVL p hB hgb


theorem affine_boundary_mixed_from_trace_barrier_with_source_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u w density : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (hw : ContDiff ℝ 2 w)
    (J : ClosureC2Jet u U) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hup : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hden : ContDiffOn ℝ 1 density U)
    (hud : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = (density x : ℂ))
    (hdenne : ∀ x ∈ U, density x ≠ 0)
    (K : E →L[ℂ] E) (c : E) (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hsource : ∀ x ∈ U, |fderiv ℝ density x (c+K x)/density x| ≤ A)
    (hVL : ∀ x ∈ U, complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹ (realHessian (fun y => u y-w y) x) ≤
      -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re))
    {x : E} (hx : x ∈ frontier U) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ y ∈ frontier U, |J.derivative y (c+K y)| ≤ B*‖y-x‖^2) :
    ∀ y ∈ closure U,
      |J.hessian x (y-x) (c+K x)+J.derivative x (K (y-x))| ≤
        2*(A+B)*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) := by
  let V : E → ℝ := fun y => u y-w y
  let g : E → ℝ := fun y => J.derivative y (c+K y)
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hVb : ∀ y ∈ frontier U, V y = 0 := fun y hy => by simp only [V,hub y hy,hwb y hy,sub_self]
  have hbound := closure_affine_jet_abs_le_trace_barrier_with_source_two hU hK e hab hu J hub hup hden hud hdenne K c htrace hA hsource
    (J.continuous_value.sub hw.continuous.continuousOn) (hu2.sub hw.contDiffOn) hVb hVL x hB hgb
  have hgx : g x = 0 := by
    have hh := hgb x hx
    have hh0 : |g x| ≤ 0 := by
      simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,g] using hh
    exact abs_eq_zero.mp (le_antisymm hh0 (abs_nonneg _))
  have hxcl := frontier_subset_closure hx
  have hdg := (closureJet_derivative_hasFDerivWithinAt hU hconv hu2 J hxcl).clm_apply
    (((K.restrictScalars ℝ).hasFDerivAt.const_add c).hasFDerivWithinAt)
  change HasFDerivWithinAt g _ (closure U) x at hdg
  have hdV := (closureJet_hasFDerivWithinAt hU hconv
    (hu2.differentiableOn (by norm_num)) J hxcl).sub
    ((hw.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
  change HasFDerivWithinAt V _ (closure U) x at hdV
  have hp := derivative_le_of_quadratic_comparison_on_convex_set hconv.closure hxcl hdg hdV
    hgx (hVb x hx) (2*(A+B)) B (fun y hy => (le_abs_self _).trans (hbound y hy))
  have hn := derivative_le_of_quadratic_comparison_on_convex_set hconv.closure hxcl hdg.neg hdV
    (by simp only [Pi.neg_apply,hgx,neg_zero]) (hVb x hx) (2*(A+B)) B
    (fun y hy => (neg_le_abs _).trans (hbound y hy))
  intro y hy
  have hpy := hp y hy
  have hny := hn y hy
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply] at hpy hny
  change J.derivative x (K (y-x))+J.hessian x (y-x) (c+K x) ≤
    2*(A+B)*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) at hpy
  change -(J.derivative x (K (y-x))+J.hessian x (y-x) (c+K x)) ≤
    2*(A+B)*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) at hny
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end PowerConvexity
