import PowerConvexity.Calculus.QuadraticPerturbationStableTwo

/-! # Continuation on moving physical domains

The PDE is always evaluated on the physical domain φ_t(U), in the fixed
complex frame. No nonlinear pullback is asserted to preserve the equation.
The actual solution family and joint pulled-back spectral continuity remain
explicit analytic inputs; this theorem constructs neither one.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem constantDensity_quadratic_moving_deformation_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hCU : IsCompact (closure U)) (hneU : U.Nonempty)
    (φ : ℝ → E ≃ₜ E) (u : ℝ → E → ℝ) (ρ : ℝ → ℂ)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure (φ t '' U), ContDiffAt ℝ 4 (u t) x)
    (hρ : ∀ t ∈ Icc (0:ℝ) 1, ρ t ≠ 0)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ φ t '' U,
      (complexHessian e (fun j => Complex.I • e j) (u t) x).det = ρ t)
    (hpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure (φ t '' U),
      (complexHessian e (fun j => Complex.I • e j) (u t) x).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure (φ t '' U), u t x+q x < 0)
    (h0 : ∀ x ∈ closure (φ 0 '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u 0) x)
    (hbd : ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ frontier (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x)
    (hcontinuous :
      letI := quadraticL2NormedAddCommGroup μ hK hKi
      letI : TopologicalSpace (quadraticSubmodule E) :=
        (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
      let P := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
      ContinuousOn (fun z : ℝ × (E × P) => modifiedSigmaTwo e (fun j => Complex.I • e j)
        (fun y => u z.1 y+z.2.2.val.val y) (φ z.1 z.2.1))
        (Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ {q : P | quadraticL2Energy μ K q.val.val ≤ ε}))) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
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
  let G : ℝ → E → P → ℝ := fun t x p => modifiedSigmaTwo a b
    (fun y => u t y+(F p).val y) (φ t x)
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hε.le
  have hneS : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ ε
    simpa [quadraticL2Energy] using hε.le
  have hclass (p : P) : IsPluriharmonicQuadratic a b (F p).val := ⟨p.val.property,p.property⟩
  have hopen (t : ℝ) : IsOpen (φ t '' U) := (φ t).isOpenMap U hU
  have hconn' (t : ℝ) : IsPreconnected (φ t '' U) := hconn.image _ (φ t).continuous.continuousOn
  have hcompact (t : ℝ) : IsCompact (closure (φ t '' U)) := by
    rw [← (φ t).image_closure]
    exact hCU.image (φ t).continuous
  have hclosure (t : ℝ) {x : E} (hx : x ∈ closure U) : φ t x ∈ closure (φ t '' U) := by
    rw [← (φ t).image_closure]
    exact ⟨x,hx,rfl⟩
  have hfront (t : ℝ) {x : E} (hx : x ∈ frontier U) : φ t x ∈ frontier (φ t '' U) := by
    rw [← (φ t).image_frontier]
    exact ⟨x,hx,rfl⟩
  have ht0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hinitial := pluriharmonic_quadratic_perturbation_stable_two μ hK hKi e
    (hopen 0) (hconn' 0) (hcompact 0) (hneU.image (φ 0))
    (hu 0 ht0) (hρ 0 ht0) (hdet 0 ht0) (hpos 0 ht0) hε (hneg 0 ht0) h0 (hbd 0 ht0)
  have hfrontne : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hneU,by
    intro he
    apply hCU.ne_univ
    simp [he]⟩
  obtain ⟨x₀,hx₀⟩ := hfrontne
  have hcontact : ∀ t ∈ Ioc (0:ℝ) 1,
      (∀ x ∈ closure U, ∀ p ∈ S, 0 ≤ G t x p) →
      ∀ x ∈ U, ∀ p ∈ S, 0 < G t x p := by
    intro t ht hnonneg
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
    have hN (q : E → ℝ) (hq : IsPluriharmonicQuadratic a b q)
        (hEq : quadraticL2Energy μ K q ≤ ε) (y : E) (hy : y ∈ φ t '' U) :
        0 ≤ modifiedSigmaTwo a b (fun z => u t z+q z) y := by
      obtain ⟨x,hx,rfl⟩ := hy
      let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
      exact hnonneg x (subset_closure hx) p (show p ∈ S from hEq)
    have hanchor := pluriharmonic_quadratic_family_interior_anchor_two μ hK hKi a b
      (fun x hx => (hu t htI x hx).of_le (by norm_num)) (hpos t htI) hε.le (hneg t htI)
      (frontier_subset_closure (hfront t hx₀))
      (fun q hq hEq => hbd t htI q hq hEq (φ t x₀) (hfront t hx₀))
    have hstrict := pluriharmonic_quadratic_nonnegative_family_positive_two μ hK hKi e
      (hopen t) (hconn' t)
      (fun x hx => (hu t htI x (subset_closure hx)).contDiffWithinAt)
      (hρ t htI) (hdet t htI) (fun x hx => hpos t htI x (subset_closure hx)) hε
      (fun q hq hEq x hx => hneg t htI q hq hEq x (subset_closure hx)) hN hanchor
    intro x hx p hp
    exact hstrict _ (hclass p) hp (φ t x) ⟨x,hx,rfl⟩
  have hresult := compactFamily_positive_by_first_contact (F := G) hU hCU hneU hS hneS hcontinuous
    (fun x hx p hp => hinitial _ (hclass p) hp (φ 0 x) (hclosure 0 hx))
    (fun t ht x hx p hp => hbd t ht _ (hclass p) hp (φ t x) (hfront t hx)) hcontact
  intro t ht q hq hEq y hy
  rw [← (φ t).image_closure] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  exact hresult t ht x hx p (show p ∈ S from hEq)

end PowerConvexity
