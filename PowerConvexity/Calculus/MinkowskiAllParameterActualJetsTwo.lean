import PowerConvexity.Calculus.MinkowskiZeroParameterActualJetsTwo
import PowerConvexity.Calculus.MinkowskiPositiveParameterSpectrumTwo

/-! # Actual joint jets on the entire parameter interval.
The ball endpoint uses the proved interior small-CMA estimate; positive
parameters use the already proved actual boundary estimates. No jet oracle
or power-convexity endpoint is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E] [Nontrivial E]
attribute [local instance] zphRealSpace zphRealModule zphDualSpace zphDualModule
  zphDualTopology zphHessSpace zphHessModule zphHessTopology
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_actual_jets_continuousAt_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho D : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hD : 0 ≤ D)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ D) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ D)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {s : I} {x : E} (hx : x ∈ minkowskiDomain s A (ball (0 : E) R)) :
    ContinuousAt (fun p : I × E => fderiv ℝ (u p.1) p.2) (s,x) ∧
    ContinuousAt (fun p : I × E => realHessian (u p.1) p.2) (s,x) := by
  by_cases hs : 0 < (s : ℝ)
  · exact minkowski_family_actual_jets_continuousAt_of_pos_two hA hconv hK hboundary
      e hab hR hrho hD hballA hballB hAb hBb hu J hs hx
  · have hs0 : s = (⟨0,by norm_num⟩ : I) :=
      Subtype.ext (le_antisymm (le_of_not_gt hs) s.2.1)
    subst s
    have hxB : x ∈ ball (0 : E) R := by
      simpa only [minkowskiDomain_zero ⟨0,hballA (mem_closedBall_self hrho.le)⟩] using hx
    exact minkowski_family_actual_jets_continuousAt_zero_two hA hconv e hab
      hR hrho hD hballA hballB hAb hBb hu hxB

theorem minkowski_family_actual_jets_continuousOn_distanceClosure_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho D eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hD : 0 ≤ D) (heps : 0 < eps)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ D) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ D)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
    ContinuousOn (fun p : I × E => u p.1 p.2) S ∧
    ContinuousOn (fun p : I × E => fderiv ℝ (u p.1) p.2) S ∧
    ContinuousOn (fun p : I × E => realHessian (u p.1) p.2) S := by
  let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A (ball 0 R) :=
    (distanceInteriorDomain_closure_subset (hV p.1) heps hp).1
  have hval : ContinuousOn (fun p : I × E => u p.1 p.2) S := by
    apply (hu.joint_continuous hab hA isOpen_ball hconv (convex_ball 0 R)
      hrho hD hballA hballB hAb hBb).continuousOn.congr
    intro p hp
    simp only [Set.indicator_of_mem (hcl p hp)]
  have hj (p : I × E) (hp : p ∈ S) := minkowski_family_actual_jets_continuousAt_two
    hA hconv hK hboundary e hab hR hrho hD hballA hballB hAb hBb hu J (hcl p hp)
  exact ⟨hval,fun p hp => (hj p hp).1.continuousWithinAt,
    fun p hp => (hj p hp).2.continuousWithinAt⟩

end PowerConvexity
