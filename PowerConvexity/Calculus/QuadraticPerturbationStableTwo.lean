import PowerConvexity.Calculus.QuadraticEnvelopePositivityTwo
import PowerConvexity.Calculus.QuadraticBoundaryAnchorTwo
import PowerConvexity.Calculus.QuadraticRadiusScaling
import PowerConvexity.Calculus.QuadraticScaledContinuityTwo
import PowerConvexity.Analysis.CompactFamilyFirstContact

/-! # Actual perturbation stability in dimension two

This is the spectral (and therefore positive real Hessian) content of the
frozen proposition. C4 on the closure is only required for the compact interior
subdomain; the original Dirichlet boundary is not being assigned C4 regularity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB CHS.Calculus.complexHessian CHS.Calculus.pureHessian complexGradient
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem pluriharmonic_quadratic_perturbation_stable_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hCU : IsCompact (closure U)) (hneU : U.Nonempty)
    {u : E → ℝ} (hu : ∀ x ∈ closure U, ContDiffAt ℝ 4 u x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = ρ)
    (hpos : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ y ∈ closure U, u y+q y < 0)
    (h0 : ∀ x ∈ closure U, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x)
    (hbd : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ frontier U,
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) :
    ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure U,
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
  let v : ℝ → P → E → ℝ := fun t p y => u y+t*(F p).val y
  let G : ℝ → E → P → ℝ := fun t x p => modifiedSigmaTwo a b (v t p) x
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hε.le
  have hneS : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ ε
    simpa [quadraticL2Energy] using hε.le
  have hclass (p : P) : IsPluriharmonicQuadratic a b (F p).val := ⟨p.val.property,p.property⟩
  have hscale (t : ℝ) (p : P) : IsPluriharmonicQuadratic a b (fun y => t*(F p).val y) :=
    IsPluriharmonicQuadratic_const_mul (hclass p) t
  have henergy (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (p : P) (hp : p ∈ S) :
      quadraticL2Energy μ K (fun y => t*(F p).val y) ≤ ε :=
    quadraticL2Energy_scaled_le μ K (F p).val hp ht
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ closure U)
      (p : P) (hp : p ∈ S) : v t p x < 0 := hneg _ (hscale t p) (henergy t ht p hp) x hx
  have hA (t : ℝ) (x : E) (hx : x ∈ closure U) (p : P) :
      (complexHessian a b (v t p) x).PosDef :=
    (strictPsh_pluriharmonic_add_iff ((hu x hx).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff (hscale t p).1 2).contDiffAt a b
      ((hscale t p).2 x)).mpr (hpos x hx)
  have hG : ContinuousOn (fun z : ℝ × (E × P) => G z.1 z.2.1 z.2.2)
      (Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ S)) :=
    quadraticFamily_scaled_spectrum_continuousOn F a b
      (fun x hx => (hu x hx).of_le (by norm_num)) hn
      (fun t ht x hx p hp => modifiedA_posDef a b (hn t ht x hx p hp) (hA t x hx p))
  have hfront : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hneU,by
    intro he
    apply hCU.ne_univ
    simp [he]⟩
  obtain ⟨x₀,hx₀⟩ := hfront
  have hcontact : ∀ t ∈ Ioc (0:ℝ) 1,
      (∀ x ∈ closure U, ∀ p ∈ S, 0 ≤ G t x p) →
      ∀ x ∈ U, ∀ p ∈ S, 0 < G t x p := by
    intro t ht hnonneg
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
    have hδ : 0 < t^2*ε := mul_pos (sq_pos_of_pos ht.1) hε
    have hδε : t^2*ε ≤ ε := by
      have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      nlinarith [mul_le_mul_of_nonneg_right ht2 hε.le]
    have hnegδ (q : E → ℝ) (hq : IsPluriharmonicQuadratic a b q)
        (hEq : quadraticL2Energy μ K q ≤ t^2*ε) : ∀ x ∈ closure U, u x+q x < 0 :=
      hneg q hq (hEq.trans hδε)
    have hNδ (q : E → ℝ) (hq : IsPluriharmonicQuadratic a b q)
        (hEq : quadraticL2Energy μ K q ≤ t^2*ε) (x : E) (hx : x ∈ U) :
        0 ≤ modifiedSigmaTwo a b (fun y => u y+q y) x := by
      obtain ⟨r,hr,hEr,he⟩ := exists_unscaled_pluriharmonic_quadratic μ K a b hq ht.1.ne' hEq
      let p : P := ⟨⟨r,hr.1⟩,hr.2⟩
      have hh := hnonneg x (subset_closure hx) p (show p ∈ S from hEr)
      change 0 ≤ modifiedSigmaTwo a b (fun y => u y+t*r y) x at hh
      rw [show (fun y => u y+t*r y) = (fun y => u y+q y) by rw [← he]] at hh
      exact hh
    have ha := pluriharmonic_quadratic_family_interior_anchor_two μ hK hKi a b
      (fun x hx => (hu x hx).of_le (by norm_num)) hpos hδ.le hnegδ
      (frontier_subset_closure hx₀) (fun q hq hEq => hbd q hq (hEq.trans hδε) x₀ hx₀)
    have hp := pluriharmonic_quadratic_nonnegative_family_positive_two μ hK hKi e hU hconn
      (fun x hx => (hu x (subset_closure hx)).contDiffWithinAt) hρ hdet
      (fun x hx => hpos x (subset_closure hx)) hδ
      (fun q hq hEq x hx => hnegδ q hq hEq x (subset_closure hx)) hNδ ha
    intro x hx p hpS
    exact hp _ (hscale t p) (quadraticL2Energy_scaled_radius_le μ K (F p).val hpS) x hx
  have hresult := compactFamily_positive_by_first_contact hU hCU hneU hS hneS hG
    (fun x hx p _ => by simpa only [G,v,zero_mul,add_zero] using h0 x hx)
    (fun t ht x hx p hp => hbd _ (hscale t p) (henergy t ht p hp) x hx) hcontact
  intro q hq hEq x hx
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  have hh := hresult 1 (by constructor <;> norm_num) x hx p (show p ∈ S from hEq)
  change 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+1*q y) x at hh
  simpa only [one_mul] using hh

end PowerConvexity
