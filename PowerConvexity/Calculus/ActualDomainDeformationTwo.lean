import PowerConvexity.Calculus.QuadraticPerturbationStableTwo
import PowerConvexity.Calculus.SpectralHessianPositivityTwo
import PowerConvexity.Analysis.VaryingDomainFirstContact

/-! # First-contact assembly on the actual domains

The physical domains are used directly, with their actual derivatives and
equations. Continuity of their actual spectral minima and boundary positivity
are the remaining analytic inputs. The conclusion is strict convexity of
`-sqrt(-u-q)`, implementing the frozen manuscript's correction at line 1173.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]
  [TopologicalSpace T] [PreconnectedSpace T]

theorem constantDensity_quadratic_actual_domain_deformation_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {V : T → Set E} (hVo : ∀ t, IsOpen (V t)) (hconv : ∀ t, Convex ℝ (V t))
    (hCV : ∀ t, IsCompact (closure (V t))) (hneV : ∀ t, (V t).Nonempty)
    (u : T → E → ℝ) (ρ : T → ℂ)
    (hu : ∀ t, ∀ x ∈ closure (V t), ContDiffAt ℝ 4 (u t) x)
    (hρ : ∀ t, ρ t ≠ 0)
    (hdet : ∀ t, ∀ x ∈ V t,
      (complexHessian e (fun j => Complex.I • e j) (u t) x).det = ρ t)
    (hpos : ∀ t, ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (u t) x).PosDef)
    {η : ℝ} (hη : 0 < η)
    (hneg : ∀ t, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ closure (V t), u t x+q x < 0)
    (t₀ : T) (h0 : ∀ x ∈ closure (V t₀),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t₀) x)
    (hbd : ∀ t, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ frontier (V t),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x)
    (hm : Continuous (fun t => sInf ((fun x =>
      sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
        {q | quadraticL2Energy μ K q.val.val ≤ η})) '' closure (V t)))) :
    ∀ t, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η →
      (∀ x ∈ closure (V t),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x) ∧
      StrictConvexOn ℝ (V t) (powerTransform (fun y => u t y+q y)) := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule a b
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let S : Set P := {q | quadraticL2Energy μ K q.val.val ≤ η}
  let G : T → E → P → ℝ := fun t x p => modifiedSigmaTwo a b
    (fun y => u t y+(F p).val y) x
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hη.le
  have hneS : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ η
    simpa [quadraticL2Energy] using hη.le
  have hclass (p : P) : IsPluriharmonicQuadratic a b (F p).val := ⟨p.val.property,p.property⟩
  have hG (t : T) : ContinuousOn (fun z : E × P => G t z.1 z.2) (closure (V t) ×ˢ S) := by
    intro z hz
    have hn := hneg t _ (hclass z.2) hz.2 z.1 hz.1
    have hA := (strictPsh_pluriharmonic_add_iff ((hu t z.1 hz.1).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt a b
      ((hclass z.2).2 z.1)).mpr (hpos t z.1 hz.1)
    exact (quadraticFamily_joint_modifiedSigmaTwo_continuousAt F a b
      ((hu t z.1 hz.1).of_le (by norm_num)) hn (modifiedA_posDef a b hn hA)).continuousWithinAt
  have hinitial := pluriharmonic_quadratic_perturbation_stable_two μ hK hKi e
    (hVo t₀) (hconv t₀).isPreconnected (hCV t₀) (hneV t₀)
    (hu t₀) (hρ t₀) (hdet t₀) (hpos t₀) hη (hneg t₀) h0 (hbd t₀)
  have hcontact (t : T)
      (hnonneg : ∀ x ∈ closure (V t), ∀ p ∈ S, 0 ≤ G t x p) :
      ∀ x ∈ V t, ∀ p ∈ S, 0 < G t x p := by
    have hfront : (frontier (V t)).Nonempty := nonempty_frontier_iff.mpr ⟨hneV t,by
      intro he
      apply (hCV t).ne_univ
      simp only [he,closure_univ]⟩
    obtain ⟨x₀,hx₀⟩ := hfront
    have hN (q : E → ℝ) (hq : IsPluriharmonicQuadratic a b q)
        (hEq : quadraticL2Energy μ K q ≤ η) (x : E) (hx : x ∈ V t) :
        0 ≤ modifiedSigmaTwo a b (fun y => u t y+q y) x := by
      let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
      exact hnonneg x (subset_closure hx) p (show p ∈ S from hEq)
    have hanchor := pluriharmonic_quadratic_family_interior_anchor_two μ hK hKi a b
      (fun x hx => (hu t x hx).of_le (by norm_num)) (hpos t) hη.le (hneg t)
      (frontier_subset_closure hx₀) (fun q hq hEq => hbd t q hq hEq x₀ hx₀)
    have hstrict := pluriharmonic_quadratic_nonnegative_family_positive_two μ hK hKi e
      (hVo t) (hconv t).isPreconnected
      (fun x hx => (hu t x (subset_closure hx)).contDiffWithinAt)
      (hρ t) (hdet t) (fun x hx => hpos t x (subset_closure hx)) hη
      (fun q hq hEq x hx => hneg t q hq hEq x (subset_closure hx)) hN hanchor
    intro x hx p hp
    exact hstrict _ (hclass p) hp x hx
  have hresult := varyingDomainFamily_positive_of_no_contact hVo hCV hneV hS hneS hG hm t₀
    (fun x hx p hp => hinitial _ (hclass p) hp x hx)
    (fun t x hx p hp => hbd t _ (hclass p) hp x hx) hcontact
  intro t q hq hEq
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  have hpositive : ∀ x ∈ closure (V t),
      0 < modifiedSigmaTwo a b (fun y => u t y+q y) x :=
    fun x hx => hresult t x hx p (show p ∈ S from hEq)
  have hC2 : ContDiffOn ℝ 2 (u t) (V t) :=
    fun x hx => ((hu t x (subset_closure hx)).of_le (by norm_num)).contDiffWithinAt
  refine ⟨hpositive,?_⟩
  apply strictConvexOn_power_of_modifiedSigmaTwo e (hVo t) (hconv t)
    (hC2.add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffOn)
    (fun x hx => hneg t q hq hEq x (subset_closure hx))
    (fun x hx => (strictPsh_pluriharmonic_add_iff
      ((hu t x (subset_closure hx)).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt a b (hq.2 x)).mpr
        (hpos t x (subset_closure hx)))
    (fun x hx => hpositive x (subset_closure hx))

end PowerConvexity
