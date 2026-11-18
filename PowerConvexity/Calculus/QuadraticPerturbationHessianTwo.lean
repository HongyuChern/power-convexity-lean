import PowerConvexity.Calculus.QuadraticPerturbationStableTwo
import PowerConvexity.Calculus.SpectralHessianPositivityTwo
import PowerConvexity.Calculus.UniformQuadraticRobustness

/-! # The positive real Hessian form of perturbation stability

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

theorem pluriharmonic_quadratic_perturbation_Hessian_stable_two
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
    (h0 : ∀ x ∈ closure U, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v)
    (hbd : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ frontier U, ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform (fun y => u y+q y)) x v v) :
    ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure U, ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform (fun y => u y+q y)) x v v := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hz : IsPluriharmonicQuadratic a b (fun _ : E => 0) :=
    ⟨(quadraticSubmodule E).zero_mem,(pluriharmonicQuadraticSubmodule a b).zero_mem⟩
  have hEz : quadraticL2Energy μ K (fun _ : E => 0) ≤ ε := by
    simpa [quadraticL2Energy] using hε.le
  have huneg (x : E) (hx : x ∈ closure U) : u x < 0 := by
    simpa only [add_zero] using hneg _ hz hEz x hx
  have hAq (q : E → ℝ) (hq : IsPluriharmonicQuadratic a b q) (x : E) (hx : x ∈ closure U) :
      (complexHessian a b (fun y => u y+q y) x).PosDef :=
    (strictPsh_pluriharmonic_add_iff ((hu x hx).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt a b (hq.2 x)).mpr (hpos x hx)
  have hσ := pluriharmonic_quadratic_perturbation_stable_two μ hK hKi e hU hconn hCU hneU
    hu hρ hdet hpos hε hneg
    (fun x hx => (modifiedSigmaTwo_pos_iff_powerHessian_pos e
      ((hu x hx).of_le (by norm_num)) (huneg x hx) (hpos x hx)).mpr (h0 x hx))
    (fun q hq hEq x hx => (modifiedSigmaTwo_pos_iff_powerHessian_pos e
      (((hu x (frontier_subset_closure hx)).of_le (by norm_num)).add
        (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt)
      (hneg q hq hEq x (frontier_subset_closure hx))
      (hAq q hq x (frontier_subset_closure hx))).mpr (hbd q hq hEq x hx))
  intro q hq hEq x hx
  exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e
    (((hu x hx).of_le (by norm_num)).add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt)
    (hneg q hq hEq x hx) (hAq q hq x hx)).mp (hσ q hq hEq x hx)

end PowerConvexity
