import PowerConvexity.Calculus.MinkowskiStrongActualBoundaryHolderTwo
import PowerConvexity.Calculus.MinkowskiStrongDefiningActualCollarTwo

/-! # Actual common truncation collar and exhaustion on strong Minkowski domains

All analytic and moving-geometric inputs of the common collar are proved
from the genuine strong defining geometry and the same actual classical
family. One positive thickness precedes every smaller positive truncation
and every parameter. The exhaustion conclusion is on each original full
Minkowski domain. Classical-family existence is the only PDE-existence
input; no solution modulus, derivative bound, or geometry oracle remains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E] [Nontrivial E]
attribute [local instance] zphRealSpace zphRealModule zphDualSpace zphDualModule
  zphDualTopology zphHessSpace zphHessModule zphHessTopology
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_strong_defining_actual_common_truncation_sigma_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x ∈ frontier A, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hFH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
 :
    ∃ thickness > 0, ∀ eps : ℝ, 0 < eps → eps < thickness →
      ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  obtain ⟨radius,hrad,hrad1,alpha,ha,ha1,C,hC,hbound⟩ :=
    strong_defining_minkowski_actual_boundary_holder_two hA hconv hK hF hFb hdelta hFH
      e hab hR hrho hballA hballB hAb hBb
  have hholder : ∀ t : I, ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ z ∈ closure (minkowskiDomain t A (ball 0 R)), ‖z-c‖ < radius →
        ‖(J t).hessian z-(J t).hessian c‖ ≤ C*‖z-c‖^alpha :=
    fun t => hbound t (u t) (hu t) (J t)
  exact minkowski_strong_defining_actual_common_collar_from_boundary_holder_two
    hA hconv hK hF hFb hdelta hFH e hab hR hrho hL hballA hballB hAb hBb hu J
    ha hrad hholder


theorem minkowski_strong_defining_actual_original_domain_exhaustion_two
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {Q : Set E} (hQK : IsCompact Q) (hQi : (interior Q).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x ∈ frontier A, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hFH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
 :
    ∀ t : I,
      (∀ x ∈ minkowskiDomain t A (ball 0 R),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  obtain ⟨radius,hrad,hrad1,alpha,ha,ha1,C,hC,hbound⟩ :=
    strong_defining_minkowski_actual_boundary_holder_two hA hconv hK hF hFb hdelta hFH
      e hab hR hrho hballA hballB hAb hBb
  have hholder : ∀ t : I, ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ z ∈ closure (minkowskiDomain t A (ball 0 R)), ‖z-c‖ < radius →
        ‖(J t).hessian z-(J t).hessian c‖ ≤ C*‖z-c‖^alpha :=
    fun t => hbound t (u t) (hu t) (J t)
  exact minkowski_strong_defining_actual_exhaustion_from_boundary_holder_two
    mu hQK hQi hA hconv hK hF hFb hdelta hFH e hab hR hrho hL hballA hballB hAb hBb hu J
    ha hrad hholder

end PowerConvexity
