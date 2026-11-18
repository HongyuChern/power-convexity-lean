import PowerConvexity.Calculus.ClosureJetContDiff
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # The actual closure jet along a boundary chart

The two chain-rule identities connect the prescribed jet to genuine boundary
parametrizations. No extension of u through the boundary is used. Producing
a particular geometric chart and identifying its shape operator remain
separate geometric obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closureJet_boundary_chart_derivative
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    {N : Set F} (hN : IsOpen N) {γ : F → E} (hγ : DifferentiableOn ℝ γ N)
    (hγb : MapsTo γ N (frontier U)) {x : F} (hx : x ∈ N) :
    (J.derivative (γ x)).comp (fderiv ℝ γ x) = 0 := by
  have hnear : ∀ᶠ y in 𝓝 x, γ y ∈ closure U := by
    filter_upwards [hN.mem_nhds hx] with y hy
    exact frontier_subset_closure (hγb hy)
  have hd := (closureJet_hasFDerivWithinAt hU hconv hu J
    (frontier_subset_closure (hγb hx))).comp_hasFDerivAt x
    ((hγ x hx).differentiableAt (hN.mem_nhds hx)).hasFDerivAt hnear
  have he : u ∘ γ =ᶠ[𝓝 x] (0 : F → ℝ) := by
    filter_upwards [hN.mem_nhds hx] with y hy
    exact hb (γ y) (hγb hy)
  rw [← hd.fderiv, he.fderiv_eq]
  simp

theorem closureJet_boundary_chart_hessian
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    {N : Set F} (hN : IsOpen N) {γ : F → E} (hγ : ContDiffOn ℝ 2 γ N)
    (hγb : MapsTo γ N (frontier U)) {x : F} (hx : x ∈ N) (v w : F) :
    J.hessian (γ x) (fderiv ℝ γ x v) (fderiv ℝ γ x w) +
      J.derivative (γ x) (fderiv ℝ (fderiv ℝ γ) x v w) = 0 := by
  have hnear : ∀ᶠ y in 𝓝 x, γ y ∈ closure U := by
    filter_upwards [hN.mem_nhds hx] with y hy
    exact frontier_subset_closure (hγb hy)
  have hγx := hγ.contDiffAt (hN.mem_nhds hx)
  have hD := (closureJet_derivative_hasFDerivWithinAt hU hconv hu J
    (frontier_subset_closure (hγb hx))).comp_hasFDerivAt x
    (hγx.differentiableAt (by norm_num)).hasFDerivAt hnear
  have hH := ((hγx.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hh := hD.clm_comp hH
  have he : (fun y => (J.derivative (γ y)).comp (fderiv ℝ γ y)) =ᶠ[𝓝 x]
      (0 : F → F →L[ℝ] ℝ) := by
    filter_upwards [hN.mem_nhds hx] with y hy
    exact closureJet_boundary_chart_derivative hU hconv
      (hu.differentiableOn (by norm_num)) J hb hN
      (hγ.differentiableOn (by norm_num)) hγb hy
  have hz := he.fderiv_eq (𝕜 := ℝ)
  have hhh := hh.fderiv
  simp only [Function.comp_apply] at hhh
  rw [hhh] at hz
  have hvw := congrArg (fun H : F →L[ℝ] F →L[ℝ] ℝ => H v w) hz
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    Function.comp_apply, fderiv_zero, ContinuousLinearMap.zero_apply, Pi.zero_apply,
    add_comm] using hvw

end PowerConvexity
