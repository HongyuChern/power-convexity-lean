import PowerConvexity.Calculus.StrictConvexity
import PowerConvexity.Calculus.RealHessianRules

/-! # Convexity implies nonnegative actual real Hessians in the interior -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_nonneg_of_convexOn {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hconv : ConvexOn ℝ U u)
    {x : E} (hx : x ∈ U) (v : E) : 0 ≤ realHessian u x v v := by
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x+v)
  let S : Set ℝ := γ ⁻¹' U
  let f : ℝ → ℝ := u ∘ γ
  have hS : IsOpen S := hU.preimage AffineMap.lineMap_continuous
  have h0 : (0 : ℝ) ∈ S := by
    change γ 0 ∈ U
    simpa [γ] using hx
  have hfc : ConvexOn ℝ S f := hconv.comp_affineMap γ
  have hfd : ∀ t ∈ S, DifferentiableAt ℝ f t := by
    intro t ht
    have hγ : HasDerivAt (γ : ℝ → E) ((x+v)-x) t := AffineMap.hasDerivAt_lineMap
    exact (hu.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num) |>.comp t hγ.differentiableAt
  have hmono := hfc.monotoneOn_deriv hfd
  have hsecond := hmono.derivWithin_nonneg (x := 0)
  rw [derivWithin_of_mem_nhds (hS.mem_nhds h0)] at hsecond
  change 0 ≤ deriv (deriv (fun t : ℝ => u (AffineMap.lineMap x (x+v) t))) 0 at hsecond
  have hux : ContDiffAt ℝ 2 u (AffineMap.lineMap x (x+v) (0 : ℝ)) := by
    simpa using hu.contDiffAt (hU.mem_nhds hx)
  rw [deriv2_comp_lineMap x (x+v) 0 hux] at hsecond
  simpa using hsecond

theorem realBlockHessian_posSemidef_of_convexOn {ι : Type*} [Fintype ι]
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hconv : ConvexOn ℝ U u)
    {x : E} (hx : x ∈ U) (a b : ι → E) :
    (realBlockHessian a b u x).PosSemidef :=
  realBlockHessian_posSemidef_of_quadratic_nonneg (hu.contDiffAt (hU.mem_nhds hx)) a b
    (realHessian_nonneg_of_convexOn hU hu hconv hx)

end PowerConvexity
