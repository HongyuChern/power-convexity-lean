import PowerConvexity.Calculus.MinkowskiBallStartRadiusTwo

/-! # A strictly positive actual ball minimum on the constructed common ball

This proves m(0)>0 for the same L2 ball used for all parameters. Positivity
of m(0), together with continuity only at positive parameters, does not
assert a positive initial interval. The zero-parameter control is still open.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem quadratic_actual_compact_minimum_positive_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {S : Set E} (hS : IsCompact S) (hne : S.Nonempty) {u : E → ℝ}
    (hu : ∀ x ∈ S, ContDiffAt ℝ 2 u x)
    (hpos : ∀ x ∈ S, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy mu K q ≤ eta → ∀ x ∈ S, u x+q x < 0)
    (hsigma : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy mu K q ≤ eta → ∀ x ∈ S,
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) :
    0 < sInf ((fun x =>
      sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
        modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q.val.val y) x) ''
        {q | quadraticL2Energy mu K q.val.val ≤ eta})) '' S) := by
  letI := quadraticL2NormedAddCommGroup mu hQK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup mu hQK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace mu hQK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let Q := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
  let F : Q →ₗ[ℝ] quadraticSubmodule E := Q.subtype
  let Qball : Set Q := {q | quadraticL2Energy mu K q.val.val ≤ eta}
  let G : E → Q → ℝ := fun x q =>
    modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+(F q).val y) x
  have hQ : IsCompact Qball :=
    pluriharmonicQuadraticL2Ball_isCompact mu hQK hKi e (fun j => Complex.I • e j) heta
  have hQne : Qball.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy mu K (0 : E → ℝ) ≤ eta
    simpa [quadraticL2Energy] using heta
  have hclass (q : Q) : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (F q).val :=
    ⟨q.val.property,q.property⟩
  have hG : ContinuousOn (fun z : E × Q => G z.1 z.2) (S ×ˢ Qball) := by
    intro z hz
    have hn := hneg _ (hclass z.2) hz.2 z.1 hz.1
    have hA := (strictPsh_pluriharmonic_add_iff (hu z.1 hz.1)
      (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt e (fun j => Complex.I • e j)
      ((hclass z.2).2 z.1)).mpr (hpos z.1 hz.1)
    exact (quadraticFamily_joint_modifiedSigmaTwo_continuousAt F e (fun j => Complex.I • e j)
      (hu z.1 hz.1) hn (modifiedA_posDef e (fun j => Complex.I • e j) hn hA)).continuousWithinAt
  obtain ⟨x,hx,he,_⟩ := hS.exists_sInf_image_eq_and_le hne
    (compactLowerEnvelope_continuousOn hQ hG)
  change 0 < sInf ((compactLowerEnvelope Qball G) '' S)
  rw [he]
  exact compactLowerEnvelope_pos_on hQ hQne hG hx
    (fun q hq => hsigma _ (hclass q) hq x hx)

variable [CompleteSpace E]

theorem minkowski_family_exists_common_radius_ball_minimum_positive_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ eta : ℝ, 0 < eta ∧
      (∀ t : I, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy mu K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          u t x+q x < 0) ∧
      (let m := fun t : I => sInf ((fun x =>
          sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
            modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
            {q | quadraticL2Energy mu K q.val.val ≤ eta})) ''
          closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps))
       0 < m ⟨0,by norm_num⟩ ∧ ∀ s : I, 0 < (s : ℝ) → ContinuousAt m s) := by
  obtain ⟨eta,heta,hnegative,hball,hm⟩ := minkowski_family_exists_common_ball_start_radius_two
    mu hQK hKi hA hconv hK hboundary e hab hR hrho hL heps hepsrho
    hballA hballB hAb hBb hu J
  refine ⟨eta,heta,hnegative,?_,hm⟩
  let t0 : I := ⟨0,by norm_num⟩
  have hgeo := minkowski_distanceInterior_uniform_geometry hA isOpen_ball
    hconv (convex_ball 0 R) hrho heps hepsrho hballA hballB hAb hBb t0
  have hU : IsOpen (minkowskiDomain t0 A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t0
  apply quadratic_actual_compact_minimum_positive_two mu hQK hKi e hgeo.2.2.2.1
    ⟨0,subset_closure hgeo.2.2.1⟩
    (fun x hx => ((hu t0).1.contDiffAt (hU.mem_nhds (hgeo.2.2.2.2 hx))).of_le (by norm_num))
    (fun x hx => (hu t0).2.2.1 x (hgeo.2.2.2.2 hx)) heta.le
    (fun q hq hEq x hx => hnegative t0 q hq.1 hEq x hx) hball

end PowerConvexity
