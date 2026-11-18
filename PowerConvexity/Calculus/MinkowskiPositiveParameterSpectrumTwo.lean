import PowerConvexity.Calculus.MinkowskiPositiveParameterJetsTwo
import PowerConvexity.Calculus.MinkowskiComplexFrameMinimumTwo
import PowerConvexity.Analysis.MinkowskiLocalDistanceMinimum

/-! # Actual unperturbed and perturbed minima at every positive parameter

No boundary-Hessian estimate is assumed. Classical-family existence is still
an input. A radius in the perturbed statement is the same actual L2 radius in
the negativity premise and in both nested infima.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E] [Nontrivial E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_actual_jets_continuousOn_positive_distanceClosure_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L) (heps : 0 < eps)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    let S := {p : I × E | 0 < (p.1 : ℝ) ∧
      p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
    ContinuousOn (fun p : I × E => u p.1 p.2) S ∧
    ContinuousOn (fun p : I × E => fderiv ℝ (u p.1) p.2) S ∧
    ContinuousOn (fun p : I × E => realHessian (u p.1) p.2) S := by
  let S := {p : I × E | 0 < (p.1 : ℝ) ∧
    p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A (ball 0 R) :=
    (distanceInteriorDomain_closure_subset (hV p.1) heps hp.2).1
  have hval : ContinuousOn (fun p : I × E => u p.1 p.2) S := by
    apply (hu.joint_continuous hab hA isOpen_ball hconv (convex_ball 0 R)
      hrho hL hballA hballB hAb hBb).continuousOn.congr
    intro p hp
    simp only [Set.indicator_of_mem (hcl p hp)]
  have hj (p : I × E) (hp : p ∈ S) := minkowski_family_actual_jets_continuousAt_of_pos_two
    hA hconv hK hboundary e hab hR hrho hL hballA hballB hAb hBb hu J hp.1 (hcl p hp)
  exact ⟨hval,fun p hp => (hj p hp).1.continuousWithinAt,
    fun p hp => (hj p hp).2.continuousWithinAt⟩

theorem minkowski_family_sigma_minimum_continuousAt_of_pos_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {s : I} (hs : 0 < (s : ℝ)) :
    ContinuousAt (fun t : I => sInf ((fun x =>
      modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ''
      closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps))) s := by
  let S := {p : I × E | 0 < (p.1 : ℝ) ∧
    p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A (ball 0 R) :=
    (distanceInteriorDomain_closure_subset (hV p.1) heps hp.2).1
  have hreg (p : I × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (u p.1) p.2 :=
    ((hu p.1).1.contDiffAt ((hV p.1).mem_nhds (hcl p hp))).of_le (by norm_num)
  have hneg (p : I × E) (hp : p ∈ S) : u p.1 p.2 < 0 :=
    strictPshDirichlet_negative (hV p.1)
      (minkowskiDomain_isCompact_closure hAb hBb p.1.2.1 p.1.2.2)
      (hu p.1).continuous_closure ((hu p.1).1.of_le (by norm_num))
      (hu p.1).2.2.2.2 e (fun j => Complex.I • e j) (hu p.1).2.2.1 p.2 (hcl p hp)
  have hj := minkowski_family_actual_jets_continuousOn_positive_distanceClosure_two
    hA hconv hK hboundary e hab hR hrho hL heps hballA hballB hAb hBb hu J
  have hsig : ContinuousOn (fun p : I × E =>
      modifiedSigmaTwo e (fun j => Complex.I • e j) (u p.1) p.2) S :=
    actualFamily_modifiedSigmaTwo_continuousOn_of_jets e (fun j => Complex.I • e j)
      (fun p : I × E => u p.1) Prod.snd hreg hj.1 hj.2.1 hj.2.2 hneg
      (fun p hp => (hu p.1).2.2.1 p.2 (hcl p hp))
  exact minkowski_distanceInterior_minimum_continuousAt_of_pos hA isOpen_ball hconv (convex_ball 0 R)
    hrho hL heps hepsrho hballA hballB hAb hBb hsig hs

variable [MeasurableSpace E] [BorelSpace E]

theorem minkowski_family_quadratic_minimum_continuousAt_of_pos_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps eta : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho) (heta : 0 ≤ eta)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hnegative : ∀ t : I, 0 < (t : ℝ) → ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy mu K q ≤ eta →
      ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps), u t x+q x < 0)
    {s : I} (hs : 0 < (s : ℝ)) :
    ContinuousAt (fun t : I => sInf ((fun x =>
      sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
        {q | quadraticL2Energy mu K q.val.val ≤ eta})) ''
      closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps))) s := by
  let S := {p : I × E | 0 < (p.1 : ℝ) ∧
    p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball 0 R)) eps)}
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A (ball 0 R) :=
    (distanceInteriorDomain_closure_subset (hV p.1) heps hp.2).1
  have hreg (p : I × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (u p.1) p.2 :=
    ((hu p.1).1.contDiffAt ((hV p.1).mem_nhds (hcl p hp))).of_le (by norm_num)
  have hpos (p : I × E) (hp : p ∈ S) :
      (complexHessian e (fun j => Complex.I • e j) (u p.1) p.2).PosDef :=
    (hu p.1).2.2.1 p.2 (hcl p hp)
  have hj := minkowski_family_actual_jets_continuousOn_positive_distanceClosure_two
    hA hconv hK hboundary e hab hR hrho hL heps hballA hballB hAb hBb hu J
  letI := quadraticL2NormedAddCommGroup mu hQK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup mu hQK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace mu hQK hKi
  letI : FiniteDimensional ℝ (quadraticSubmodule E) := quadraticSubmodule_finiteDimensional
  let Q := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
  let F := Q.subtype
  let Qball : Set Q := {q | quadraticL2Energy mu K q.val.val ≤ eta}
  have hQ : IsCompact Qball :=
    pluriharmonicQuadraticL2Ball_isCompact mu hQK hKi e (fun j => Complex.I • e j) heta
  have hq (q : Q) : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (F q).val :=
    ⟨q.val.property,q.property⟩
  have hEnvelope : ContinuousOn (compactLowerEnvelope Qball
      (fun p q => modifiedSigmaTwo e (fun j => Complex.I • e j)
        (fun y => u p.1 y+(F q).val y) p.2)) S :=
    quadratic_spectralEnvelope_continuousOn_of_base_jets_two e (fun j => Complex.I • e j)
      F (fun p : I × E => u p.1) Prod.snd hQ hreg continuous_snd.continuousOn
      hj.1 hj.2.1 hj.2.2 hpos (fun q _ => hq q)
      (fun q hEq p hp => hnegative p.1 hp.1 _ (hq q) hEq p.2 hp.2)
  exact minkowski_distanceInterior_minimum_continuousAt_of_pos hA isOpen_ball hconv (convex_ball 0 R)
    hrho hL heps hepsrho hballA hballB hAb hBb hEnvelope hs

end PowerConvexity
