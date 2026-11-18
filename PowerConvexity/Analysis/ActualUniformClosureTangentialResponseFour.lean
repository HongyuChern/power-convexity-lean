import PowerConvexity.Calculus.ClassicalDefiningNormalTwo
import PowerConvexity.Calculus.ClosureJetBoundaryChart

/-! # Genuine zero trace of the tangential closure response

The boundary response is evaluated using the actual closure derivative. A
regular defining function identifies its normal, so tangency gives zero.
There is also a chart formulation needing no Monge--Ampere equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

/-- The boundary value is the genuine closure derivative, not the total
ambient derivative of an arbitrary extension. -/
def actualClosureTangentialResponseFour {U : Set E} {u : E → ℝ}
    (J : ClosureC2Jet u U) (T : E → E) (x : E) : ℝ := J.derivative x (T x)

theorem actual_closure_tangential_response_eq_four {U : Set E} {u : E → ℝ}
    (J : ClosureC2Jet u U) (T : E → E) :
    EqOn (actualClosureTangentialResponseFour J T) (fun x => fderiv ℝ u x (T x)) U := by
  intro x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L (T x)) (J.derivative_eq hx)

theorem actual_closure_tangential_response_eventually_eq_four {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (J : ClosureC2Jet u U) (T : E → E) {x : E} (hx : x ∈ U) :
    actualClosureTangentialResponseFour J T =ᶠ[𝓝 x] (fun y => fderiv ℝ u y (T y)) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact actual_closure_tangential_response_eq_four J T hy

theorem actual_closure_tangential_response_regular_four {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (J : ClosureC2Jet u U) {T : E → E}
    (hu : ContDiffOn ℝ 3 u U) (hT : ContDiffOn ℝ 2 T U) :
    ContDiffOn ℝ 2 (actualClosureTangentialResponseFour J T) U := by
  apply ((hu.fderiv_of_isOpen hU (m := 2) (by norm_num)).clm_apply hT).congr
  intro x hx
  exact actual_closure_tangential_response_eq_four J T hx

theorem actual_closure_tangential_response_continuous_four {U : Set E}
    {u : E → ℝ} (J : ClosureC2Jet u U) {T : E → E}
    (hT : ContinuousOn T (closure U)) :
    ContinuousOn (actualClosureTangentialResponseFour J T) (closure U) :=
  J.continuous_derivative.clm_apply hT

theorem actual_closure_tangential_response_zero_of_chart_four
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0)
    {V : Set F} (hV : IsOpen V) {gamma : F → E} (hgamma : DifferentiableOn ℝ gamma V)
    (hboundary : MapsTo gamma V (frontier U)) {y : F} (hy : y∈V)
    {T : E → E} (tau : F) (hT : T (gamma y)=fderiv ℝ gamma y tau) :
    actualClosureTangentialResponseFour J T (gamma y)=0 := by
  have hh := congrArg (fun L : F →L[ℝ] ℝ => L tau)
    (closureJet_boundary_chart_derivative hU hconv hu J hb hV hgamma hboundary hy)
  simpa only [actualClosureTangentialResponseFour,hT,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] using hh

end General

section NormalIdentification
variable [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_closure_tangential_response_zero_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det=1)
    {T : E → E} {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x=0) (hDf : fderiv ℝ f x≠0)
    (hdef : ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) (hTan : fderiv ℝ f x (T x)=0) :
    actualClosureTangentialResponseFour J T x=0 := by
  obtain ⟨lam,_,he⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two hU hconv hK
    hu J hb a b hab hpsh hdet hx hf hfx hDf hdef
  simp only [actualClosureTangentialResponseFour,he,smul_apply,smul_eq_mul,hTan,mul_zero]

end NormalIdentification
end PowerConvexity
