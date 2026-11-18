import PowerConvexity.Calculus.QuadraticMinimumAttained
import PowerConvexity.Calculus.QuadraticRayleighContactGeneral
import PowerConvexity.Algebra.GeneralizedRayleighMinimum

/-! # General-dimensional attainment on the genuine L2 ball

Minimize the continuous generalized Rayleigh quotient on the product with a
unit sphere. No continuity or smoothness assumption on selected roots is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder Matrix BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrixQuadraticForm_continuousAt {X : Type*} [TopologicalSpace X]
    {M : X → Matrix ι ι ℂ} {v : X → ι → ℂ} {p : X}
    (hM : ∀ i j, ContinuousAt (fun y => M y i j) p)
    (hv : ∀ i, ContinuousAt (fun y => v y i) p) :
    ContinuousAt (fun y => (star (v y) ⬝ᵥ (M y *ᵥ v y)).re) p := by
  apply Complex.continuous_re.continuousAt.comp
  change ContinuousAt (fun y => ∑ i, star (v y i)*(∑ j, M y i j*v y j)) p
  exact tendsto_finsetSum _ (fun i _ => (continuous_star.continuousAt.comp (hv i)).mul
    (tendsto_finsetSum _ (fun j _ => (hM i j).mul (hv j))))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem quadraticFamily_generalizedRayleigh_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P × (ι → ℂ)}
    (hneg : u x+(F p.1).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p.1).val y) x).PosDef)
    (hv : p.2 ≠ 0) :
    ContinuousAt (fun y : P × (ι → ℂ) => generalizedRayleigh
      (modifiedSchur a b (fun z => u z+(F y.1).val z) x)
      (modifiedA a b (fun z => u z+(F y.1).val z) x) y.2) p := by
  have hcoord (i : ι) : ContinuousAt (fun y : P × (ι → ℂ) => y.2 i) p :=
    (continuous_apply i).continuousAt.comp continuousAt_snd
  apply (matrixQuadraticForm_continuousAt (fun i j =>
    (quadraticFamily_modifiedSchur_contDiffAt F a b hu hneg hA i j 0).continuousAt.comp
      continuousAt_fst) hcoord).div
      (matrixQuadraticForm_continuousAt (fun i j =>
        (quadraticFamily_modifiedA_contDiffAt F a b hu hneg i j 0).continuousAt.comp
          continuousAt_fst) hcoord)
  exact (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hv)).1.ne'

theorem exists_quadraticFamily_minimizer_on_compact_general
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {S : Set P} (hS : IsCompact S) (hne : S.Nonempty)
    (hneg : ∀ p ∈ S, u x+(F p).val x < 0)
    (hpos : ∀ p ∈ S, (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) :
    ∃ p ∈ S, ∀ r ∈ S,
      modifiedSigma a b (fun y => u y+(F p).val y) x ≤
        modifiedSigma a b (fun y => u y+(F r).val y) x := by
  let V := ι → ℂ
  let T : Set V := Metric.sphere 0 1
  have hT : T.Nonempty := by
    obtain ⟨p,hp⟩ := hne
    obtain ⟨v,hv,_⟩ := exists_unit_generalizedRayleigh_minimum (hpos p hp)
      (modifiedB_transpose (hu.add (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt) a b)
    exact ⟨v,by simpa [T,Metric.mem_sphere,dist_zero_right] using hv⟩
  let R : P × V → ℝ := fun y => generalizedRayleigh
    (modifiedSchur a b (fun z => u z+(F y.1).val z) x)
    (modifiedA a b (fun z => u z+(F y.1).val z) x) y.2
  have hR : ContinuousOn R (S ×ˢ T) := by
    intro p hp
    apply (quadraticFamily_generalizedRayleigh_continuousAt F a b hu
      (hneg p.1 hp.1) (hpos p.1 hp.1) ?_).continuousWithinAt
    intro hz
    have hv : ‖p.2‖ = 1 := by simpa [T,Metric.mem_sphere,dist_zero_right] using hp.2
    simpa [hz] using hv
  obtain ⟨p,hp,hmin⟩ := (hS.prod (isCompact_sphere (0:V) 1)).exists_isMinOn (hne.prod hT) hR
  refine ⟨p.1,hp.1,?_⟩
  intro r hr
  have hBp := modifiedB_transpose
    (hu.add (IsQuadraticPolynomial_contDiff (F p.1).property 2).contDiffAt) a b
  have hBr := modifiedB_transpose
    (hu.add (IsQuadraticPolynomial_contDiff (F r).property 2).contDiffAt) a b
  have hpv : p.2 ≠ 0 := by
    intro hz
    have hv : ‖p.2‖ = 1 := by simpa [T,Metric.mem_sphere,dist_zero_right] using hp.2
    simpa [hz] using hv
  obtain ⟨v,hv,hev⟩ := exists_unit_generalizedRayleigh_minimum (hpos r hr) hBr
  have hvT : v ∈ T := by simpa [T,Metric.mem_sphere,dist_zero_right] using hv
  exact (schur_minimum_le_generalizedRayleigh (hpos p.1 hp.1) hBp hpv).trans
    ((hmin (show (r,v) ∈ S ×ˢ T from ⟨hr,hvT⟩)).trans_eq hev)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_pluriharmonic_quadratic_minimizer_general
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (a b : ι → E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε → u x+q x < 0)
    (hpos : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      (modifiedA a b (fun y => u y+q y) x).PosDef) :
    ∃ q : E → ℝ, IsPluriharmonicQuadratic a b q ∧ quadraticL2Energy μ K q ≤ ε ∧
      ∀ h : E → ℝ, IsPluriharmonicQuadratic a b h → quadraticL2Energy μ K h ≤ ε →
        modifiedSigma a b (fun y => u y+q y) x ≤ modifiedSigma a b (fun y => u y+h y) x := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule a b
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let S : Set P := {q | quadraticL2Energy μ K q.val.val ≤ ε}
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hε
  have hne : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0:E → ℝ) ≤ ε
    simpa [quadraticL2Energy] using hε
  obtain ⟨q,hq,hmin⟩ := exists_quadraticFamily_minimizer_on_compact_general F a b hu hS hne
    (fun p hp => hneg _ ⟨p.val.property,p.property⟩ hp)
    (fun p hp => hpos _ ⟨p.val.property,p.property⟩ hp)
  refine ⟨q.val.val,⟨q.val.property,q.property⟩,hq,?_⟩
  intro h hh hE
  let r : P := ⟨⟨h,hh.1⟩,hh.2⟩
  exact hmin r (show r ∈ S from hE)

end PowerConvexity
