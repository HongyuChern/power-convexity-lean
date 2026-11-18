import PowerConvexity.Calculus.QuadraticPerturbationStableTwo

/-! # The actual common-quadratic minimum cannot equal zero

This is a fixed-domain contact theorem. Boundary positivity for the very same
quadratic L2 ball is explicit. No parameter continuity or initial positivity
is assumed, and no Dirichlet power-convexity endpoint is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def actualQuadraticSpectralMinimumTwo
    (μ : Measure E) (K : Set E) (e : Module.Basis (Fin 2) ℂ E)
    (η : ℝ) (V : Set E) (u : E → ℝ) : ℝ :=
  sInf ((fun x => sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
    modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q.val.val y) x) ''
      {q | quadraticL2Energy μ K q.val.val ≤ η})) '' closure V)

theorem actualQuadraticSpectralMinimumTwo_attains
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {V : Set E} (hV : IsCompact (closure V)) (hne : V.Nonempty)
    {u : E → ℝ} (hu : ∀ x ∈ closure V, ContDiffAt ℝ 2 u x)
    (hp : ∀ x ∈ closure V, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {η : ℝ} (hη : 0 ≤ η)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ closure V, u x+q x < 0) :
    ∃ x ∈ closure V, ∃ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q ∧
      quadraticL2Energy μ K q ≤ η ∧
      actualQuadraticSpectralMinimumTwo μ K e η V u =
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x ∧
      ∀ y ∈ closure V, ∀ r : E → ℝ,
        IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r →
        quadraticL2Energy μ K r ≤ η →
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun z => u z+q z) x ≤
          modifiedSigmaTwo e (fun j => Complex.I • e j) (fun z => u z+r z) y := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let S : Set P := {q | quadraticL2Energy μ K q.val.val ≤ η}
  let G : E → P → ℝ := fun x q =>
    modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+(F q).val y) x
  have hS : IsCompact S :=
    pluriharmonicQuadraticL2Ball_isCompact μ hK hKi e (fun j => Complex.I • e j) hη
  have hSne : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ η
    simpa [quadraticL2Energy] using hη
  have hclass (q : P) : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (F q).val :=
    ⟨q.val.property,q.property⟩
  have hG : ContinuousOn (fun z : E × P => G z.1 z.2) (closure V ×ˢ S) := by
    intro z hz
    have hn := hneg _ (hclass z.2) hz.2 z.1 hz.1
    have hA := (strictPsh_pluriharmonic_add_iff (hu z.1 hz.1)
      (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt e (fun j => Complex.I • e j)
      ((hclass z.2).2 z.1)).mpr (hp z.1 hz.1)
    exact (quadraticFamily_joint_modifiedSigmaTwo_continuousAt F e (fun j => Complex.I • e j)
      (hu z.1 hz.1) hn (modifiedA_posDef e (fun j => Complex.I • e j) hn hA)).continuousWithinAt
  obtain ⟨x,hx,he,hmin⟩ := hV.exists_sInf_image_eq_and_le (hne.mono subset_closure)
    (compactLowerEnvelope_continuousOn hS hG)
  obtain ⟨q,hq,heq,_⟩ := compactLowerEnvelope_attains_on hS hSne hG hx
  refine ⟨x,hx,(F q).val,hclass q,hq,he.trans heq,?_⟩
  intro y hy r hr hEr
  let p : P := ⟨⟨r,hr.1⟩,hr.2⟩
  have hh := (hmin y hy).trans (compactLowerEnvelope_le_on hS hSne hG hy
    (show p ∈ S from hEr))
  rw [heq] at hh
  exact hh

theorem actualQuadraticSpectralMinimumTwo_le
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {V : Set E} (hV : IsCompact (closure V)) (hne : V.Nonempty)
    {u : E → ℝ} (hu : ∀ x ∈ closure V, ContDiffAt ℝ 2 u x)
    (hp : ∀ x ∈ closure V, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {η : ℝ} (hη : 0 ≤ η)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ closure V, u x+q x < 0)
    {x : E} (hx : x ∈ closure V) {q : E → ℝ}
    (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
    (hEq : quadraticL2Energy μ K q ≤ η) :
    actualQuadraticSpectralMinimumTwo μ K e η V u ≤
      modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x := by
  obtain ⟨y,hy,r,hr,hEr,he,hmin⟩ := actualQuadraticSpectralMinimumTwo_attains
    μ hK hKi e hV hne hu hp hη hneg
  rw [he]
  exact hmin x hx q hq hEq

variable [ProperSpace E] [Nontrivial E]

theorem actualQuadraticSpectralMinimumTwo_ne_zero_of_boundary_positive
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {V : Set E} (hVo : IsOpen V) (hconn : IsPreconnected V)
    (hV : IsCompact (closure V)) (hne : V.Nonempty)
    {u : E → ℝ} (hu : ∀ x ∈ closure V, ContDiffAt ℝ 4 u x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ x ∈ V, (complexHessian e (fun j => Complex.I • e j) u x).det = ρ)
    (hp : ∀ x ∈ closure V, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {η : ℝ} (hη : 0 < η)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ closure V, u x+q x < 0)
    (hbd : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η → ∀ x ∈ frontier V,
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) :
    actualQuadraticSpectralMinimumTwo μ K e η V u ≠ 0 := by
  intro hz
  have hu2 : ∀ x ∈ closure V, ContDiffAt ℝ 2 u x := fun x hx => (hu x hx).of_le (by norm_num)
  have hnonneg (q : E → ℝ) (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hEq : quadraticL2Energy μ K q ≤ η) (x : E) (hx : x ∈ V) :
      0 ≤ modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x := by
    have hh := actualQuadraticSpectralMinimumTwo_le μ hK hKi e hV hne hu2 hp hη.le hneg
      (subset_closure hx) hq hEq
    simpa only [hz] using hh
  have hfront : (frontier V).Nonempty := nonempty_frontier_iff.mpr ⟨hne,by
    intro he
    apply hV.ne_univ
    simp only [he,closure_univ]⟩
  obtain ⟨z,hzV⟩ := hfront
  have hanchor := pluriharmonic_quadratic_family_interior_anchor_two μ hK hKi e
    (fun j => Complex.I • e j) hu2 hp hη.le hneg (frontier_subset_closure hzV)
    (fun q hq hEq => hbd q hq hEq z hzV)
  have hstrict := pluriharmonic_quadratic_nonnegative_family_positive_two μ hK hKi e
    hVo hconn (fun x hx => (hu x (subset_closure hx)).contDiffWithinAt) hρ hdet
    (fun x hx => hp x (subset_closure hx)) hη
    (fun q hq hEq x hx => hneg q hq hEq x (subset_closure hx)) hnonneg hanchor
  obtain ⟨x,hx,q,hq,hEq,he,_⟩ := actualQuadraticSpectralMinimumTwo_attains
    μ hK hKi e hV hne hu2 hp hη.le hneg
  have hpositive : 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x := by
    by_cases hi : x ∈ V
    · exact hstrict q hq hEq x hi
    · exact hbd q hq hEq x (by rw [hVo.frontier_eq]; exact ⟨hx,hi⟩)
  linarith

end PowerConvexity
