import PowerConvexity.Calculus.TraceBarrierBoundaryComparisonTwo
import PowerConvexity.Calculus.ClosureJetDifferentiability

/-! # Actual mixed boundary jets from the affine-field trace barrier

Differentiation is within the genuine convex closure, using the continuous
extension of the interior first and second derivatives. No ambient extension
of the unknown solution is introduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem derivative_le_of_quadratic_comparison_on_convex_set
    {S : Set E} (hS : Convex ℝ S) {x : E} (hx : x ∈ S)
    {g V : E → ℝ} {Dg DV : E →L[ℝ] ℝ}
    (hg : HasFDerivWithinAt g Dg S x) (hV : HasFDerivWithinAt V DV S x)
    (hgx : g x = 0) (hVx : V x = 0) (A B : ℝ)
    (hbound : ∀ z ∈ S, g z ≤ A*V z+B*‖z-x‖^2) :
    ∀ y ∈ S, Dg (y-x) ≤ A*DV (y-x) := by
  let f : E → ℝ := fun z => g z-A*V z-B*‖z-x‖^2
  have hq : HasFDerivAt (fun z : E => ‖z-x‖^2) (0 : E →L[ℝ] ℝ) x := by
    have hh := ((hasFDerivAt_id x).sub_const x).norm_sq
    simpa only [id_eq,sub_self,map_zero,ContinuousLinearMap.zero_comp,smul_zero] using hh
  have hd := (hg.sub (hV.const_mul A)).sub (hq.hasFDerivWithinAt.const_mul B)
  change HasFDerivWithinAt f _ S x at hd
  have hm : IsMaxOn f S x := by
    intro y hy
    change g y-A*V y-B*‖y-x‖^2 ≤ g x-A*V x-B*‖x-x‖^2
    rw [hgx,hVx,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,mul_zero,
      sub_zero,sub_zero]
    linarith [hbound y hy]
  intro y hy
  have hh := hm.localize.hasFDerivWithinAt_nonpos hd
    (sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hx hy))
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply,smul_eq_mul,mul_zero,sub_zero,sub_nonpos] using hh

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem closure_affine_jet_abs_le_trace_barrier_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u V : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (J : ClosureC2Jet u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    (K : E →L[ℂ] E) (c : E) (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    (hVL : ∀ x ∈ U, complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹ (realHessian V x) ≤
      -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, |J.derivative x (c+K x)| ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, |J.derivative x (c+K x)| ≤ 2*B*V x+B*‖x-p‖^2 := by
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
  have hgL (x : E) (hx : x ∈ U) : complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹ (realHessian g x) = 0 := by
    rw [show realHessian g x = realHessian (fun y => fderiv ℝ u y (c+K y)) x from
      (heq x hx).fderiv.fderiv_eq]
    exact complex_affine_field_contraction_zero_two e K c htrace hU hu hud hx
  exact linearized_function_abs_le_trace_barrier_two hU hK e (fun j => Complex.I • e j) hab
    J.continuous_value (hu.of_le (by norm_num)) hub hup hud hgc hg hVc hV hVb hgL hVL p hB hgb

theorem affine_boundary_mixed_from_trace_barrier_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u w : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (hw : ContDiff ℝ 2 w)
    (J : ClosureC2Jet u U) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hup : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    (K : E →L[ℂ] E) (c : E) (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    (hVL : ∀ x ∈ U, complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹ (realHessian (fun y => u y-w y) x) ≤
      -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re))
    {x : E} (hx : x ∈ frontier U) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ y ∈ frontier U, |J.derivative y (c+K y)| ≤ B*‖y-x‖^2) :
    ∀ y ∈ closure U,
      |J.hessian x (y-x) (c+K x)+J.derivative x (K (y-x))| ≤
        2*B*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) := by
  let V : E → ℝ := fun y => u y-w y
  let g : E → ℝ := fun y => J.derivative y (c+K y)
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hVb : ∀ y ∈ frontier U, V y = 0 := fun y hy => by simp only [V,hub y hy,hwb y hy,sub_self]
  have hbound := closure_affine_jet_abs_le_trace_barrier_two hU hK e hab hu J hub hup hud K c htrace
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
    hgx (hVb x hx) (2*B) B (fun y hy => (le_abs_self _).trans (hbound y hy))
  have hn := derivative_le_of_quadratic_comparison_on_convex_set hconv.closure hxcl hdg.neg hdV
    (by simp only [Pi.neg_apply,hgx,neg_zero]) (hVb x hx) (2*B) B
    (fun y hy => (neg_le_abs _).trans (hbound y hy))
  intro y hy
  have hpy := hp y hy
  have hny := hn y hy
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply] at hpy hny
  change J.derivative x (K (y-x))+J.hessian x (y-x) (c+K x) ≤
    2*B*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) at hpy
  change -(J.derivative x (K (y-x))+J.hessian x (y-x) (c+K x)) ≤
    2*B*(J.derivative x (y-x)-fderiv ℝ w x (y-x)) at hny
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end PowerConvexity
