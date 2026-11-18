import PowerConvexity.Calculus.ChordGlobalConvexity
import PowerConvexity.Calculus.ScalarChordMaximum
import PowerConvexity.Calculus.ScalarDirichlet

/-! # Scalar initial convexity from the proved two-point maximum argument

The boundary decay input is explicit. This is not yet the manuscript endpoint
until the smooth-domain Dirichlet data are shown to imply that input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus

theorem scalarPower_convexOn_closure_of_boundary_decay
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : ℂ → ℝ} {ρ : ℝ}
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ))
    (hdecay : HasQuadraticBoundaryDecay (powerTransform u) U) :
    ConvexOn ℝ (closure U) (powerTransform u) := by
  have hneg := scalarDirichlet_negative hU hK huc hu hboundary hρpos hρ
  apply convexOn_closure_of_chord_maximum hU hconv hK (powerTransform_continuousOn huc)
    (fun x hx => (powerTransform_contDiffAt (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx)).differentiableAt (by norm_num))
    (fun x hx => powerTransform_eq_zero_of_eq_zero (hboundary x hx))
    (fun x _ => neg_nonpos.mpr (Real.sqrt_nonneg (-u x))) hdecay
  intro a b ha hb hab x hx y hy hm
  have hz := hconv hx hy ha.le hb.le hab
  exact scalarPower_chordDefect_nonpos_of_localMax ha hb
    (hu.contDiffAt (hU.mem_nhds hx)) (hu.contDiffAt (hU.mem_nhds hy))
    (hu.contDiffAt (hU.mem_nhds hz)) (hneg x hx) (hneg y hy) (hneg _ hz)
    hρpos (hρ x hx) (hρ y hy) (hρ _ hz) hm

end PowerConvexity
