import PowerConvexity.Calculus.VariableDensityDirectionalGradientTwo
import PowerConvexity.Calculus.PowerBoundaryDecayTwo

/-! # Source-correct first derivative boundary maximum estimate -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem directionalGradient_variable_density_le_boundary_bound_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (hf : ContDiffOn ℝ 1 f U)
    (J : ClosureC2Jet u U) (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hp : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x) (v : E) {C M : ℝ}
    (hsource : ∀ x ∈ U,
      -C ≤ fderiv ℝ f x v/f x)
    (hM : ∀ x ∈ frontier U, J.derivative x v ≤ M) :
    ∀ x ∈ closure U, J.derivative x v ≤ M-(C/2)*u x := by
  let g : E → ℝ := fun y => J.derivative y v + -M
  have heq (x : E) (hx : x ∈ U) :
      (fun y => J.derivative y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ u y v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [J.derivative_eq hy]
  have hgc : ContinuousOn g (closure U) :=
    (J.continuous_derivative.clm_apply continuousOn_const).add
      continuousOn_const
  have hg : ContDiffOn ℝ 2 g U := by
    intro x hx
    exact ((((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).congr_of_eventuallyEq
      (heq x hx)).add contDiffAt_const |>.contDiffWithinAt
  have hgb : ∀ x ∈ frontier U, g x ≤ 0 := by
    intro x hx
    dsimp only [g]
    linarith [hM x hx]
  have hLg : ∀ x ∈ U, -C ≤ linearizedCMAOperatorTwo a b u g x := by
    intro x hx
    have heH : realHessian (fun y => J.derivative y v) x =
        realHessian (fun y => fderiv ℝ u y v) x := (heq x hx).fderiv.fderiv_eq
    dsimp only [linearizedCMAOperatorTwo,g]
    rw [realHessian_add_const,heH]
    rw [directionalDerivative_variable_density_two hU hu hf a b hdet
      (fun y hy => (hfp y hy).ne') hx v]
    exact hsource x hx
  have hh := linearizedCMAOperatorTwo_upper_barrier a b hU hK J.continuous_value
    (hu.of_le (by norm_num)) hb hp hgc hg hgb hLg
  intro x hx
  have h := hh x hx
  dsimp only [g] at h
  linarith

variable [FiniteDimensional ℝ E]

theorem closure_gradient_norm_variable_density_le_boundary_bound_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (hf : ContDiffOn ℝ 1 f U)
    (J : ClosureC2Jet u U) (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hp : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hsource : ∀ x ∈ U, ∀ v : E, |fderiv ℝ f x v/f x| ≤ C*‖v‖)
    (hboundary : ∀ x ∈ frontier U, ‖J.derivative x‖ ≤ B) :
    ∀ x ∈ closure U, ‖J.derivative x‖ ≤ B-(C/2)*u x := by
  have hdir (v : E) : ∀ x ∈ closure U,
      J.derivative x v ≤ (B-(C/2)*u x)*‖v‖ := by
    have hh := directionalGradient_variable_density_le_boundary_bound_two hU hK hu hf J hb
      a b hp hdet hfp v (C := C*‖v‖) (M := B*‖v‖)
      (fun x hx => (abs_le.mp (hsource x hx v)).1)
      (fun x hx => (le_abs_self _).trans (by
        have hv := (J.derivative x).le_opNorm v
        rw [Real.norm_eq_abs] at hv
        exact hv.trans (mul_le_mul_of_nonneg_right (hboundary x hx) (norm_nonneg v))))
    intro x hx
    have he : B*‖v‖-(C*‖v‖/2)*u x = (B-(C/2)*u x)*‖v‖ := by ring
    simpa only [he] using hh x hx
  have hnonpos := strictPshDirichlet_nonpos_closure_two hU hK J.continuous_value
    (hu.of_le (by norm_num)) hb a b hp
  intro x hx
  have hM : 0 ≤ B-(C/2)*u x := by
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ C/2 from div_nonneg hC (by norm_num)) (hnonpos x hx)
    linarith
  apply (J.derivative x).opNorm_le_bound hM
  intro v
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_,hdir v x hx⟩
  have hh := hdir (-v) x hx
  rw [map_neg,norm_neg] at hh
  linarith

end PowerConvexity
