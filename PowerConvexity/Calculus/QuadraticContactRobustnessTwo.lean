import PowerConvexity.Calculus.QuadraticFamilyQuantitativeTwo
import PowerConvexity.Calculus.SpectralHessianSemidefiniteTwo

/-! # The quantitative positive base Hessian at a nonnegative family contact

This is the robustness step used at the limiting deformation parameter. It
needs only actual C2 jets at the contact, not an assumed positive Hessian.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem quadratic_nonnegative_spectrum_family_uniform_Hessian_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {K X : Set E}
    (hK : IsCompact K) (hX : IsCompact X) (e : Module.Basis (Fin 2) ℂ E)
    {u : E → ℝ} (hu : ∀ x ∈ X, ContDiffAt ℝ 2 u x)
    (hpos : ∀ x ∈ X, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ X, u x+q x < 0)
    (hσ : ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ X,
      0 ≤ modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X, ∀ v : E,
      C*‖v‖^2 ≤ realHessian (powerTransform u) x v v := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hz : IsPluriharmonicQuadratic a b (fun _ : E => 0) :=
    ⟨(quadraticSubmodule E).zero_mem,(pluriharmonicQuadraticSubmodule a b).zero_mem⟩
  have hEz : quadraticL2Energy μ K (fun _ : E => 0) ≤ ε := by
    simpa [quadraticL2Energy] using hε.le
  have hn (x : E) (hx : x ∈ X) : u x < 0 := by
    simpa only [add_zero] using hneg _ hz hEz x hx
  apply quadratic_family_uniform_powerHessian_lower μ hK hX a hu hn hε
  intro q hq hEq x hx
  have hA : (complexHessian a b (fun y => u y+q y) x).PosDef :=
    (strictPsh_pluriharmonic_add_iff (hu x hx)
      (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt a b (hq.2 x)).mpr (hpos x hx)
  exact (modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg e
    ((hu x hx).add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt)
    (hneg q hq hEq x hx) hA).mp (hσ q hq hEq x hx)

end PowerConvexity
