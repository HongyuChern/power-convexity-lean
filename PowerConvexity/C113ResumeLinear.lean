import PowerConvexity.C112ResumeLinear
import PowerConvexity.Analysis.ActualNormalizedCoefficientScaleTwo

/-! # Actual normalization, weak transport, regularity and physical scale

This continues the C112P183 narrow call.  Every property below belongs to the
same constructed coefficient, and the weak function is the actual pullback.
No classical representative or linear inverse is assumed or asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem c113_normalized_actual_weak_regular_divergence_scale_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hpos : (A.a x₀).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E,
      (actualLinearPullbackCoeffTwo G A).a (G.symm x₀) = 1 ∧
      (∀ i j, ContDiffOn ℝ 1
        (fun z => (actualLinearPullbackCoeffTwo G A).a z i j) (G ⁻¹' U)) ∧
      (∀ z ∈ G ⁻¹' U, ∀ j,
        (∑ i, fderiv ℝ (fun y => (actualLinearPullbackCoeffTwo G A).a y i j) z
          (EuclideanSpace.single i 1)) = 0) ∧
      ActualScalarWeakEquationTwo (actualLinearPullbackCoeffTwo G A)
        (fun z => f (G z)) (fun z => u (G z)) ∧
      ∀ epsilon > 0, ∃ r > 0, r ≤ 1 ∧ closedBall (G.symm x₀) (2*r) ⊆ G ⁻¹' U ∧
        ∀ z ∈ closedBall (0 : E) 1, ∀ v : E,
          ‖v - matMulE ((actualLinearPullbackCoeffTwo G A).a (G.symm x₀+r • z)) v‖ ≤
            (epsilon * ‖z‖) * ‖v‖ := by
  obtain ⟨G,hfreeze,hweak⟩ :=
    c112_resume_normalized_actual_weak_transport hU hUb A x₀ hpos hf hu
  have hreg' := actual_linear_pullback_coeff_contDiffOn_two G A hreg
  refine ⟨G,hfreeze,hreg',
    actual_linear_pullback_coeff_divergence_free_two hU G A hreg hdiv,hweak,?_⟩
  intro epsilon hepsilon
  exact actual_C1_coefficient_small_physical_scale_two (hU.preimage G.continuous)
    hreg' (by simpa only [mem_preimage,G.apply_symm_apply] using hx₀) hfreeze hepsilon

end PowerConvexity
