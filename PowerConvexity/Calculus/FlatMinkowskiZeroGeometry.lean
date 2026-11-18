import PowerConvexity.Calculus.MinkowskiZeroParameterGeometryObstruction
import PowerConvexity.Calculus.SmoothStrictDomainFlatBoundary

/-! # The frozen smooth strictly convex flat-boundary example blocks joint C2 geometry

This is an actual planar domain example, not a counterexample to the complex
two-dimensional Dirichlet theorem or to an interior PDE estimate at zero.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem flatBoundaryDomain_no_joint_C2_minkowski_defining_family_at_zero
    {R : ℝ} (hR : 0 < R) :
    ¬∃ delta > 0, delta ≤ 1 ∧ ∃ F : ℝ × ℂ → ℝ,
      ContDiffOn ℝ 2 F (ball 0 (2*delta) ×ˢ (univ : Set ℂ)) ∧
      ∀ t ∈ Icc (0 : ℝ) delta,
        ∀ z ∈ frontier (minkowskiDomain t flatBoundaryDomain (ball (0 : ℂ) R)),
          F (t,z) = 0 ∧ fderiv ℝ (fun y => F (t,y)) z ≠ 0 ∧
          (∀ᶠ y in 𝓝 z,
            y ∈ minkowskiDomain t flatBoundaryDomain (ball (0 : ℂ) R) ↔ F (t,y) < 0) := by
  rintro ⟨delta,hdelta,hdelta1,F,hF,hreg⟩
  have hconv : Convex ℝ flatBoundaryDomain := strictBoundaryChords_convex
    flatBoundaryDomain_isOpen flatBoundaryDomain_strictBoundaryChords
  have hf : ContDiffAt ℝ 2 flatBoundaryDefining Complex.I :=
    (flatBoundaryDefining_smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hfx : flatBoundaryDefining Complex.I = 0 := by norm_num [flatBoundaryDefining]
  have hvalue : fderiv ℝ flatBoundaryDefining Complex.I Complex.I = 2 := by
    rw [flatBoundaryDefining_fderiv]
    norm_num [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
  have hDf : fderiv ℝ flatBoundaryDefining Complex.I ≠ 0 := by
    intro hz
    have hh := congrArg (fun D : ℂ →L[ℝ] ℝ => D Complex.I) hz
    rw [hvalue,ContinuousLinearMap.zero_apply] at hh
    norm_num at hh
  exact no_joint_C2_regular_minkowski_defining_family_at_zero_of_flat_tangent
    flatBoundaryDomain_isOpen hconv flatBoundaryDomain_I_frontier hf hfx hDf
    (Filter.Eventually.of_forall (fun _ => Iff.rfl))
    flatBoundaryDomain_flat_tangent.1 flatBoundaryDomain_flat_tangent.2.1
    flatBoundaryDomain_flat_tangent.2.2 hR hdelta hdelta1 hF hreg

end PowerConvexity
