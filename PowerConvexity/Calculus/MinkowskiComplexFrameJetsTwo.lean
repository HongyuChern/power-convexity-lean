import PowerConvexity.Calculus.ComplexFrameCMAJets
import PowerConvexity.Analysis.MinkowskiDistanceMinimum
import PowerConvexity.Calculus.ActualJetSpectrumContinuityTwo

/-! # The actual spectral field in the physical orthonormal complex frame

This application uses the same classical functions and boundary jets as
the PDE estimate. Locally uniform boundary quadratic upper control remains
explicit; no power-convexity endpoint supplies any of the three jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Nontrivial E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_classicalDirichlet_complexFrame_jets_continuousOn_distanceClosure_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A B u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A B))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A B), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2) :
    let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)}
    ContinuousOn (fun p : I × E => u p.1 p.2) S ∧
    ContinuousOn (fun p : I × E => fderiv ℝ (u p.1) p.2) S ∧
    ContinuousOn (fun p : I × E => realHessian (u p.1) p.2) S := by
  let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)}
  have hV (t : I) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A B :=
    (distanceInteriorDomain_closure_subset (hV p.1) hε hp).1
  have hval : ContinuousOn (fun p : I × E => u p.1 p.2) S := by
    apply (hu.joint_continuous hab hAo hBo hA hB hρ hL hballA hballB hAb hBb).continuousOn.congr
    intro p hp
    simp only [Set.indicator_of_mem (hcl p hp)]
  have hj (p : I × E) (hp : p ∈ S) :=
    minkowski_classicalDirichlet_complexFrame_jets_of_boundary_upper_two e hab hAo hBo hA hB hρ hL
      hballA hballB hAb hBb hu J (hcl p hp) (hbound p.1)
  exact ⟨hval,fun p hp => (hj p hp).1.continuousWithinAt,
    fun p hp => (hj p hp).2.continuousWithinAt⟩

theorem minkowski_classicalDirichlet_complexFrame_sigma_minimum_continuous_of_boundary_upper_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A B u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A B))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A B), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2) :
    Continuous (fun t : I => sInf ((fun x => modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ''
      closure (distanceInteriorDomain (minkowskiDomain t A B) ε))) := by
  let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)}
  have hV (t : I) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hK (t : I) : IsCompact (closure (minkowskiDomain t A B)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A B :=
    (distanceInteriorDomain_closure_subset (hV p.1) hε hp).1
  have hreg (p : I × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (u p.1) p.2 :=
    ((hu p.1).1.contDiffAt ((hV p.1).mem_nhds (hcl p hp))).of_le (by norm_num)
  have hneg (p : I × E) (hp : p ∈ S) : u p.1 p.2 < 0 :=
    strictPshDirichlet_negative (hV p.1) (hK p.1) (hu p.1).continuous_closure
      ((hu p.1).1.of_le (by norm_num)) (hu p.1).2.2.2.2 e (fun j => Complex.I • e j)
      (hu p.1).2.2.1 p.2 (hcl p hp)
  have hj := minkowski_classicalDirichlet_complexFrame_jets_continuousOn_distanceClosure_two e hab
    hAo hBo hA hB hρ hL hε hballA hballB hAb hBb hu J hbound
  have hσ : ContinuousOn (fun p : I × E => modifiedSigmaTwo e (fun j => Complex.I • e j) (u p.1) p.2) S :=
    actualFamily_modifiedSigmaTwo_continuousOn_of_jets e (fun j => Complex.I • e j)
      (fun p : I × E => u p.1) Prod.snd hreg hj.1 hj.2.1 hj.2.2 hneg
      (fun p hp => (hu p.1).2.2.1 p.2 (hcl p hp))
  exact minkowski_distanceInterior_minimum_continuous hAo hBo hA hB hρ hL hε hερ
    hballA hballB hAb hBb hσ

end PowerConvexity
