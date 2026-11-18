import PowerConvexity.Calculus.MovingDomainJetDeformationTwo
import PowerConvexity.Calculus.QuadraticFamilySmallRadiusTwo

/-! # Moving-domain continuation with only unperturbed family jets as input

A single L2 radius and all perturbed joint jets are constructed here. The
physical Dirichlet family itself is still input; no existence is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem constantDensity_moving_deformation_from_base_jets_two
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
    (hneg : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure (φ t '' U), u t x < 0)
    (h0 : ∀ x ∈ closure (φ 0 '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u 0) x)
    (hbd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ frontier (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x)
    (hφ : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0:ℝ) 1 ×ˢ closure U))
    (hv : ContinuousOn (fun p : ℝ × E => u p.1 (φ p.1 p.2)) (Icc (0:ℝ) 1 ×ˢ closure U))
    (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) (φ p.1 p.2))
      (Icc (0:ℝ) 1 ×ˢ closure U))
    (hH : ContinuousOn (fun p : ℝ × E => realHessian (u p.1) (φ p.1 p.2))
      (Icc (0:ℝ) 1 ×ˢ closure U)) :
    ∃ ε > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
  let S := Icc (0:ℝ) 1 ×ˢ closure U
  let B := Icc (0:ℝ) 1 ×ˢ frontier U
  let v : ℝ × E → E → ℝ := fun p => u p.1
  let X : ℝ × E → E := fun p => φ p.1 p.2
  have hBS : B ⊆ S := fun p hp => ⟨hp.1,frontier_subset_closure hp.2⟩
  have hSK : IsCompact S := isCompact_Icc.prod hCU
  have hBK : IsCompact B := isCompact_Icc.prod (hCU.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  have hcl (p : ℝ × E) (hp : p ∈ S) : X p ∈ closure (φ p.1 '' U) := by
    rw [← (φ p.1).image_closure]
    exact ⟨p.2,hp.2,rfl⟩
  have hfront (p : ℝ × E) (hp : p ∈ B) : X p ∈ frontier (φ p.1 '' U) := by
    rw [← (φ p.1).image_frontier]
    exact ⟨p.2,hp.2,rfl⟩
  have hreg (p : ℝ × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (v p) (X p) :=
    (hu p.1 hp.1 (X p) (hcl p hp)).of_le (by norm_num)
  have hN (p : ℝ × E) (hp : p ∈ S) : v p (X p) < 0 := hneg p.1 hp.1 (X p) (hcl p hp)
  obtain ⟨εN,hεN,hnegative⟩ := exists_quadratic_L2_radius_negative_family μ hK hKi hSK v X hφ hv hN
  obtain ⟨εB,hεB,hboundary⟩ := exists_quadratic_L2_radius_negative_and_positive_sigma_family_two
    μ hK hKi e hBK v X (fun p hp => hreg p (hBS hp)) (hφ.mono hBS) (hv.mono hBS)
    (hD.mono hBS) (hH.mono hBS) (fun p hp => hN p (hBS hp))
    (fun p hp => hpos p.1 hp.1 (X p) (hcl p (hBS hp)))
    (fun p hp => hbd p.1 hp.1 (X p) (hfront p hp))
  let ε := min εN εB
  have hε : 0 < ε := lt_min hεN hεB
  have hnegative' (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (q : E → ℝ)
      (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (he : quadraticL2Energy μ K q ≤ ε) :
      ∀ x ∈ closure (φ t '' U), u t x+q x < 0 := by
    intro x hx
    rw [← (φ t).image_closure] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact hnegative q hq.1 (he.trans (min_le_left _ _)) (t,y) ⟨ht,hy⟩
  have hboundary' (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (q : E → ℝ)
      (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (he : quadraticL2Energy μ K q ≤ ε) :
      ∀ x ∈ frontier (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
    intro x hx
    rw [← (φ t).image_frontier] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact (hboundary q hq (he.trans (min_le_right _ _)) (t,y) ⟨ht,hy⟩).2
  refine ⟨ε,hε,?_⟩
  apply constantDensity_quadratic_moving_deformation_of_jets_two μ hK hKi e hU hconn hCU hneU
    φ u ρ hu hρ hdet hpos hε hnegative' h0 hboundary'
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let Q := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
  let F : Q →ₗ[ℝ] quadraticSubmodule E := Q.subtype
  let T := Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ {q : Q | quadraticL2Energy μ K q.val.val ≤ ε})
  let m : ℝ × (E × Q) → Q × (ℝ × E) := fun z => (z.2.2,(z.1,z.2.1))
  have hm : Continuous m := by fun_prop
  have hmap : MapsTo m T (univ ×ˢ S) := fun z hz => ⟨mem_univ _,hz.1,hz.2.1⟩
  have hvq := (quadraticPerturbedFamily_value_continuousOn F v X hφ hv).comp hm.continuousOn hmap
  have hDq := (quadraticPerturbedFamily_fderiv_continuousOn F v X hreg hφ hD).comp hm.continuousOn hmap
  have hHq := (quadraticPerturbedFamily_realHessian_continuousOn F v X hreg hφ hH).comp hm.continuousOn hmap
  exact ⟨hvq,hDq,hHq⟩

end PowerConvexity
