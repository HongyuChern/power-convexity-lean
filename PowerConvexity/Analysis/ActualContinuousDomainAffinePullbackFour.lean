import PowerConvexity.Analysis.ActualContinuousDomainBoundaryDataFour
import PowerConvexity.Analysis.ActualAffineScalarBoundsFour

/-! # Actual affine pullback of the continuous-source domain problem

The normalized coefficient is the actual inverse congruence. The solution
is composed with the same affine map and the source acquires exactly r^2.
All closure Holder bounds and the true zero boundary are transported.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def ActualContinuousDomainLinearDataFour.affinePullback
    {U : Set E} (hU : IsOpen U) {lam Lambda alpha Ka Kf r B I : ℝ}
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (c : E) (G : E ≃L[ℝ] E) (hr : 0 < r)
    (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hG : ‖G.toContinuousLinearMap‖ ≤ B) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I) :
    ActualContinuousDomainLinearDataFour ((fun z : E => c+G (r • z)) ⁻¹' U)
      (lam/(max 1 B)^2) (Lambda*(max 1 I)^2) alpha
      (I^2*Ka*(r*B)^alpha) (r^2*Kf*(r*B)^alpha) := by
  let F : E → E := fun z => c+G (r • z)
  let V := F ⁻¹' U
  have hFC : Continuous F := by fun_prop
  have hFD : ContDiff ℝ 2 F := by fun_prop
  have hmap : MapsTo F V U := fun _ hx => hx
  have hmapC : MapsTo F (closure V) (closure U) := hmap.closure hFC
  let A := actualAffineNormalizedCoeffFour c G hr D.coeff hmap
  have hlo : lam/(max 1 B)^2 ≤ A.lam := by
    rw [show A.lam=D.coeff.lam/(max 1 ‖G.toContinuousLinearMap‖)^2 from rfl]
    apply div_le_div₀ D.coeff.hlam.le D.lower (by positivity)
    exact pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hG) 2
  have hhi : A.Λ ≤ Lambda*(max 1 I)^2 := by
    change D.coeff.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2 ≤ Lambda*(max 1 I)^2
    apply mul_le_mul D.upper (pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hInv) 2)
      (sq_nonneg _) (D.coeff.Λ_pos.le.trans D.upper)
  refine {
    coeff := A
    source := fun z => r^2*D.source (F z)
    solution := fun z => D.solution (F z)
    lower := hlo
    upper := hhi
    positive := actual_affine_normalized_coeff_posDef_four c G hr D.coeff hmap D.positive
    regular := actual_affine_normalized_coeff_regular_four c G hr D.coeff hmap D.regular
    divergence := actual_affine_normalized_coeff_divergence_four hU c G hr D.coeff hmap D.regular D.divergence
    holder := actual_linear_scaled_congruence_holder_four G hr.le halpha hKa hB hI hG hInv hmapC D.holder
    source_continuous := continuousOn_const.mul (D.source_continuous.comp hFC.continuousOn hmap)
    source_holder := actual_affine_scalar_source_holder_four G hr.le halpha hKf hB hG hmapC D.source_holder
    solution_regular := D.solution_regular.comp hFD.contDiffOn hmap
    solution_continuous := D.solution_continuous.comp hFC.continuousOn hmapC
    equation := ?_
  }
  intro x hx
  exact actual_affine_classical_equation_transport_four G c r
    (D.solution_regular.contDiffAt (hU.mem_nhds (hmap hx))) (D.equation _ (hmap hx))

theorem ActualContinuousDomainLinearDataFour.affinePullback_zero
    {U : Set E} (hU : IsOpen U) {lam Lambda alpha Ka Kf r B I : ℝ}
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (c : E) (G : E ≃L[ℝ] E) (hr : 0 < r)
    (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hG : ‖G.toContinuousLinearMap‖ ≤ B) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I)
    (hzero : ∀ x ∈ frontier U, D.solution x=0) :
    ∀ x ∈ frontier ((fun z : E => c+G (r • z)) ⁻¹' U),
      (D.affinePullback hU c G hr halpha hKa hKf hB hI hG hInv).solution x=0 := by
  intro x hx
  exact hzero _ ((show Continuous (fun z : E => c+G (r • z)) by fun_prop).frontier_preimage_subset U hx)

theorem ActualContinuousDomainLinearDataFour.affinePullback_source_bound
    {U : Set E} (hU : IsOpen U) {lam Lambda alpha Ka Kf r B I F : ℝ}
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (c : E) (G : E ≃L[ℝ] E) (hr : 0 < r)
    (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hG : ‖G.toContinuousLinearMap‖ ≤ B) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I)
    (hbound : ∀ x ∈ closure U, |D.source x| ≤ F) :
    ∀ x ∈ closure ((fun z : E => c+G (r • z)) ⁻¹' U),
      |(D.affinePullback hU c G hr halpha hKa hKf hB hI hG hInv).source x| ≤ r^2*F := by
  have hmap : MapsTo (fun z : E => c+G (r • z))
      ((fun z : E => c+G (r • z)) ⁻¹' U) U := fun _ hx => hx
  exact actual_affine_source_bound_four G (hmap.closure (by fun_prop)) hbound

end PowerConvexity
