import PowerConvexity.Calculus.QuadraticJointSpectrumTwo
import PowerConvexity.Calculus.ComplexRealBasis
import PowerConvexity.Calculus.QuadraticSpectralSeparationTwo
import PowerConvexity.Calculus.ActualSpectralEnvelopeTwo

/-! # Actual L2 quadratic perturbations: strict positivity from contact

Compactness, joint continuity, constant density, and separation at the actual
minimizing parameter are proved, not supplied as abstract envelope premises.
The nonnegative hypothesis is the one obtained at the first contact radius.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem pluriharmonic_quadratic_nonnegative_family_positive_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = ρ)
    (hpos : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ y ∈ U, u y+q y < 0)
    (hnonneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ y ∈ U,
      0 ≤ modifiedSigmaTwo e (fun j => Complex.I • e j) (fun z => u z+q z) y)
    (hanchor : ∃ x ∈ U, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy μ K q ≤ ε →
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) :
    ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ U,
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule a b
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let S : Set P := {q | quadraticL2Energy μ K q.val.val ≤ ε}
  let v : P → E → ℝ := fun p y => u y+(F p).val y
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hε.le
  have hne : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ ε
    simpa [quadraticL2Energy] using hε.le
  have hclass (p : P) : IsPluriharmonicQuadratic a b (F p).val := ⟨p.val.property,p.property⟩
  have hv (p : P) : ContDiffOn ℝ 4 (v p) U := hu.add
    (IsQuadraticPolynomial_contDiff (F p).property 4).contDiffOn
  have hn (p : P) (hp : p ∈ S) (x : E) (hx : x ∈ U) : v p x < 0 := hneg _ (hclass p) hp x hx
  have hA (p : P) (x : E) (hx : x ∈ U) : (complexHessian a b (v p) x).PosDef :=
    (strictPsh_pluriharmonic_add_iff ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt a b ((hclass p).2 x)).mpr (hpos x hx)
  have hF : ContinuousOn (fun z : E × P => modifiedSigmaTwo a b (v z.2) z.1) (U ×ˢ S) := by
    intro z hz
    exact (quadraticFamily_joint_modifiedSigmaTwo_continuousAt F a b
      ((hu.contDiffAt (hU.mem_nhds hz.1)).of_le (by norm_num))
      (hn z.2 hz.2 z.1 hz.1) (modifiedA_posDef a b (hn z.2 hz.2 z.1 hz.1) (hA z.2 z.1 hz.1))).continuousWithinAt
  have hN (x : E) (hx : x ∈ U) :
      0 ≤ compactLowerEnvelope S (fun y p => modifiedSigmaTwo a b (v p) y) x := by
    obtain ⟨p,hp,he,_⟩ := compactLowerEnvelope_attains_on (F := fun y p => modifiedSigmaTwo a b (v p) y) hS hne hF hx
    rw [he]
    exact hnonneg _ (hclass p) hp x hx
  have hgap (x : E) (hx : x ∈ U) (p : P) (hp : p ∈ S)
      (he : modifiedSigmaTwo a b (v p) x = compactLowerEnvelope S
        (fun y q => modifiedSigmaTwo a b (v q) y) x) :
      0 < eigenDiscriminantTwo (modifiedK a b (v p) x) := by
    apply pluriharmonic_quadratic_minimizer_has_gap_two μ hK hKi e
      ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) hε
      (fun q hq hEq => hneg q hq hEq x hx) ?_ (hclass p) hp ?_
    · intro q hq hEq
      exact modifiedA_posDef a b (hneg q hq hEq x hx)
        ((strictPsh_pluriharmonic_add_iff ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))
          (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt a b (hq.2 x)).mpr (hpos x hx))
    · intro q hq hEq
      let r : P := ⟨⟨q,hq.1⟩,hq.2⟩
      change modifiedSigmaTwo a b (v p) x ≤ modifiedSigmaTwo a b (v r) x
      rw [he]
      exact compactLowerEnvelope_le_on (F := fun y p => modifiedSigmaTwo a b (v p) y) hS hne hF hx (show r ∈ S from hEq)
  have ha : ∃ x ∈ U, 0 < compactLowerEnvelope S (fun y p => modifiedSigmaTwo a b (v p) y) x := by
    obtain ⟨x,hx,hh⟩ := hanchor
    refine ⟨x,hx,compactLowerEnvelope_pos_on (F := fun y p => modifiedSigmaTwo a b (v p) y) hS hne hF hx ?_⟩
    intro p hp
    exact hh _ (hclass p) hp
  have hstrict := actual_modifiedSigmaTwo_envelope_positive (u := v) a b (complexRealBasis e) (complexRealBasis_eq_sum e) hU hconn hS hne
    (fun p _ => hv p) (fun _ => ρ) (fun _ _ => hρ)
    (fun p _ => constantDensity_pluriharmonic_add hU (hu.of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffOn a b ρ hdet
      (fun y _ => (hclass p).2 y)) hn (fun p _ => hA p) hF hN hgap ha
  intro q hq hEq x hx
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  exact (hstrict x hx).trans_le (compactLowerEnvelope_le_on (F := fun y p => modifiedSigmaTwo a b (v p) y) hS hne hF hx (show p ∈ S from hEq))

end PowerConvexity
