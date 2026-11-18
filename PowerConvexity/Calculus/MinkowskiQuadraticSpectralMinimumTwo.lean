import PowerConvexity.Calculus.MinkowskiDistanceSpectralContinuityTwo
import PowerConvexity.Calculus.QuadraticSpectralEnvelopeFromJetsTwo
import PowerConvexity.Calculus.QuadraticL2Geometry
import PowerConvexity.Analysis.CompactSmallParameterWithin

/-! # A common quadratic radius and the manuscript's moving spectral minimum

The common radius below ensures negativity and strict plurisubharmonicity
on the actual truncated closures. Joint jets then give continuity of the
infimum over the same compact quadratic ball and the same moving domains.
Boundary positivity of the spectral envelope is not asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient

local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_exists_common_quadratic_radius_continuous_minimum_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo realDirections imagDirections A B u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A B))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A B), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2) :
    ∃ η > 0,
      (∀ t : I, ∀ q : E → ℝ, IsPluriharmonicQuadratic realDirections imagDirections q →
        quadraticL2Energy μ K q ≤ η →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A B) ε),
          u t x+q x < 0 ∧
          (complexHessian realDirections imagDirections (fun y => u t y+q y) x).PosDef) ∧
      Continuous (fun t : I => sInf ((fun x =>
        sInf ((fun q : pluriharmonicQuadraticSubmodule (realDirections (n := 2)) imagDirections =>
          modifiedSigmaTwo realDirections imagDirections (fun y => u t y+q.val.val y) x) ''
          {q | quadraticL2Energy μ K q.val.val ≤ η})) ''
        closure (distanceInteriorDomain (minkowskiDomain t A B) ε))) := by
  let S : Set (I × E) :=
    {p | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)}
  have hS : IsCompact S :=
    (minkowski_distanceInterior_parameterGraphs hAo hBo hA hB hρ hL hε hερ
      hballA hballB hAb hBb).2
  have hV (t : I) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hKt (t : I) : IsCompact (closure (minkowskiDomain t A B)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A B :=
    (distanceInteriorDomain_closure_subset (hV p.1) hε hp).1
  have hreg (p : I × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (u p.1) p.2 :=
    ((hu p.1).1.contDiffAt ((hV p.1).mem_nhds (hcl p hp))).of_le (by norm_num)
  have hpos (p : I × E) (hp : p ∈ S) :
      (complexHessian realDirections imagDirections (u p.1) p.2).PosDef :=
    (hu p.1).2.2.1 p.2 (hcl p hp)
  have hneg (p : I × E) (hp : p ∈ S) : u p.1 p.2 < 0 :=
    strictPshDirichlet_negative (hV p.1) (hKt p.1) (hu p.1).continuous_closure
      ((hu p.1).1.of_le (by norm_num)) (hu p.1).2.2.2.2 realDirections imagDirections
      (hu p.1).2.2.1 p.2 (hcl p hp)
  have hj := minkowski_classicalDirichlet_jets_continuousOn_distanceClosure_two
    hAo hBo hA hB hρ hL hε hballA hballB hAb hBb hu J hbound
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI : FiniteDimensional ℝ (quadraticSubmodule E) := quadraticSubmodule_finiteDimensional
  let Q := pluriharmonicQuadraticSubmodule (realDirections (n := 2)) imagDirections
  let F : Q →ₗ[ℝ] quadraticSubmodule E := Q.subtype
  let w : I × E → E → ℝ := fun p => u p.1
  let X : I × E → E := Prod.snd
  let value : Q × (I × E) → ℝ := fun z => u z.2.1 z.2.2+(F z.1).val z.2.2
  have hvalue : ContinuousOn value (univ ×ˢ S) :=
    quadraticPerturbedFamily_value_continuousOn F w X continuous_snd.continuousOn hj.1
  have hzero (p : I × E) (hp : p ∈ S) : 0 < -value (0,p) := by
    change 0 < -(u p.1 p.2+0)
    simpa only [add_zero] using neg_pos.mpr (hneg p hp)
  obtain ⟨r,hr,hsmall⟩ := compact_small_parameter_positive_within
    (F := fun z => -value z) hS (fun p hp => (hvalue (0,p) ⟨mem_univ _,hp⟩).neg) hzero
  let Qball : Set Q := {q | quadraticL2Energy μ K q.val.val ≤ r^2}
  have hQ : IsCompact Qball :=
    pluriharmonicQuadraticL2Ball_isCompact μ hK hKi realDirections imagDirections (sq_nonneg r)
  have hq (q : Q) : IsPluriharmonicQuadratic realDirections imagDirections (F q).val :=
    ⟨q.val.property,q.property⟩
  have hnegative (q : Q) (hqball : q ∈ Qball) (p : I × E) (hp : p ∈ S) :
      u p.1 p.2+(F q).val p.2 < 0 := by
    have he : ‖q‖^2 = quadraticL2Energy μ K q.val.val := quadraticL2_norm_sq μ hK hKi q.val
    have hn : ‖q‖ ≤ r := by
      change quadraticL2Energy μ K q.val.val ≤ r^2 at hqball
      nlinarith [norm_nonneg q]
    exact neg_pos.mp (hsmall q hn p hp)
  have hpositive (q : Q) (p : I × E) (hp : p ∈ S) :
      (complexHessian realDirections imagDirections (fun y => u p.1 y+(F q).val y) p.2).PosDef :=
    (strictPsh_pluriharmonic_add_iff (hreg p hp)
      (IsQuadraticPolynomial_contDiff (F q).property 2).contDiffAt realDirections imagDirections
      ((hq q).2 p.2)).mpr (hpos p hp)
  have hEnvelope : ContinuousOn (compactLowerEnvelope Qball
      (fun p q => modifiedSigmaTwo realDirections imagDirections
        (fun y => u p.1 y+(F q).val y) p.2)) S :=
    quadratic_spectralEnvelope_continuousOn_of_base_jets_two realDirections imagDirections
      F w X hQ hreg continuous_snd.continuousOn hj.1 hj.2.1 hj.2.2 hpos
      (fun q _ => hq q) hnegative
  refine ⟨r^2,sq_pos_of_pos hr,?_,?_⟩
  · intro t q hq' he x hx
    let qP : Q := ⟨⟨q,hq'.1⟩,hq'.2⟩
    exact ⟨hnegative qP he (t,x) hx,hpositive qP (t,x) hx⟩
  · exact minkowski_distanceInterior_minimum_continuous hAo hBo hA hB hρ hL hε hερ
      hballA hballB hAb hBb hEnvelope

end PowerConvexity
