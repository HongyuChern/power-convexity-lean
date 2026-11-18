import PowerConvexity.Calculus.QuadraticFamilyQuantitativeTwo

/-! # Both conclusions of the corrected frozen perturbation-stability proposition

The initial and boundary hypotheses are the pointwise positive-Hessian
hypotheses actually used in the frozen argument. StrictConvexOn alone is not
silently substituted for them.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem paper_perturbation_stability_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hconn : IsPreconnected U)
    (hCU : IsCompact (closure U)) (hneU : U.Nonempty)
    {u : E → ℝ} (hu : ∀ x ∈ closure U, ContDiffAt ℝ 4 u x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = ρ)
    (hpos : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ y ∈ closure U, u y+q y < 0)
    (h0 : ∀ x ∈ closure U, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v)
    (hbd : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ frontier U, ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform (fun y => u y+q y)) x v v) :
    (∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → StrictConvexOn ℝ U (powerTransform (fun y => u y+q y))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closure U, ∀ v : E, v ≠ 0 →
      C*‖v‖^2 < realHessian (powerTransform u) x v v := by
  have hH := pluriharmonic_quadratic_perturbation_Hessian_stable_two μ hK hKi e
    hU hconn hCU hneU hu hρ hdet hpos hε hneg h0 hbd
  constructor
  · apply strictConvexOn_power_quadratic_family_of_Hessian e (fun j => Complex.I • e j)
      hU hconv (fun x hx => ((hu x (subset_closure hx)).of_le (by norm_num)).contDiffWithinAt)
      μ K ε
      (fun q hq hEq x hx => hneg q hq hEq x (subset_closure hx))
    exact fun q hq hEq x hx v hv => hH q hq hEq x (subset_closure hx) v hv
  · have hz : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (fun _ : E => 0) :=
      ⟨(quadraticSubmodule E).zero_mem,
        (pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).zero_mem⟩
    have hEz : quadraticL2Energy μ K (fun _ : E => 0) ≤ ε := by
      simpa [quadraticL2Energy] using hε.le
    have huneg (x : E) (hx : x ∈ closure U) : u x < 0 := by
      simpa only [add_zero] using hneg _ hz hEz x hx
    obtain ⟨C,hC,hbound⟩ := quadratic_family_uniform_powerHessian_lower μ hK hCU e
      (fun x hx => (hu x hx).of_le (by norm_num)) huneg hε (fun q hq hEq x hx v => by
        by_cases hv : v=0
        · simp [hv]
        · exact (hH q hq hEq x hx v hv).le)
    refine ⟨C/2,by linarith,?_⟩
    intro x hx v hv
    have hvp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hc := hbound x hx v
    have hhalf := mul_pos hC hvp
    nlinarith

end PowerConvexity
