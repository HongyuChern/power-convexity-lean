import PowerConvexity.Calculus.PowerChordMaximumTwo
import PowerConvexity.Calculus.PowerBoundaryDecayTwo
import PowerConvexity.Calculus.ChordGlobalConvexity
import PowerConvexity.Calculus.ConvexHessian

/-! # Initial power convexity in dimension two from actual Dirichlet data

This supplementary route eliminates a Dirichlet deformation family for initial
(non-strict) convexity. It does not assert positive real Hessians or strict chords.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem power_convexOn_closure_of_boundary_decay_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (e k : Fin 2 → E)
    (hpsh : ∀ x ∈ U, (complexHessian e k u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e k u x).det = 1)
    (hdecay : HasQuadraticBoundaryDecay (powerTransform u) U) :
    ConvexOn ℝ (closure U) (powerTransform u) := by
  have hneg := strictPshDirichlet_negative hU hK huc hu hboundary e k hpsh
  apply convexOn_closure_of_chord_maximum hU hconv hK (powerTransform_continuousOn huc)
    (fun x hx => (powerTransform_contDiffAt (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx)).differentiableAt (by norm_num))
    (fun x hx => powerTransform_eq_zero_of_eq_zero (hboundary x hx))
    (fun x _ => neg_nonpos.mpr (Real.sqrt_nonneg (-u x))) hdecay
  intro a b ha hb hab x hx y hy hm
  have hz := hconv hx hy ha.le hb.le hab
  exact power_chordDefect_nonpos_of_localMax_two e k ha hb
    (hu.contDiffAt (hU.mem_nhds hx)) (hu.contDiffAt (hU.mem_nhds hy))
    (hu.contDiffAt (hU.mem_nhds hz)) (hneg x hx) (hneg y hy) (hneg _ hz)
    (hpsh x hx) (hpsh y hy) (hpsh _ hz)
    (hdet x hx) (hdet y hy) (hdet _ hz) hm

theorem classicalDirichlet_power_convexOn_closure_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundaryRegular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    ConvexOn ℝ (closure U) (powerTransform u) :=
  power_convexOn_closure_of_boundary_decay_two hU hconv hK huc hu hboundary a b hpsh hdet
    (dirichlet_boundary_decay_of_C2_boundary_two hU hconv hK hboundaryRegular huc hu hboundary a b hab hpsh hdet)

theorem classicalDirichlet_power_convexOn_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundaryRegular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    ConvexOn ℝ U (powerTransform u) :=
  (classicalDirichlet_power_convexOn_closure_two hU hconv hK hboundaryRegular huc hu hboundary a b hab hpsh hdet).subset subset_closure hconv

end PowerConvexity
