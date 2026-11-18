import PowerConvexity.Calculus.QuadraticPerturbationHessianTwo

/-! # Uniform lower bounds and public strict convexity after stability -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem quadratic_family_uniform_powerHessian_lower
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {K X : Set E}
    (hK : IsCompact K) (hX : IsCompact X) {ι : Type*} (a : ι → E)
    {u : E → ℝ} (hu : ∀ x ∈ X, ContDiffAt ℝ 2 u x) (hneg : ∀ x ∈ X, u x < 0)
    {ε : ℝ} (hε : 0 < ε)
    (hfamily : ∀ q : E → ℝ, IsPluriharmonicQuadratic a (fun i => Complex.I • a i) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ X, ∀ v : E,
      0 ≤ realHessian (powerTransform (fun y => u y+q y)) x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X, ∀ v : E,
      C*‖v‖^2 ≤ realHessian (powerTransform u) x v v := by
  have hc : ContinuousOn u X := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  obtain ⟨R,hR,hbound⟩ := (hX.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  let m := -(R+1)
  have hm : m < 0 := by dsimp [m]; linarith
  have hlow (x : E) (hx : x ∈ X) : m ≤ u x := by
    have hh := hbound (u x) ⟨x,hx,rfl⟩
    rw [Real.norm_eq_abs] at hh
    have hleft := (abs_le.mp hh).1
    dsimp [m]
    linarith
  obtain ⟨C,hC,hest⟩ := uniform_L2_quadratic_robustness μ hK hX.isBounded a hε hm
  refine ⟨C,hC,?_⟩
  intro x hx v
  exact hest u x hx (hu x hx) (hlow x hx) (hneg x hx)
    (fun q hq hEq w => hfamily q hq hEq x hx w) v

theorem strictConvexOn_power_quadratic_family_of_Hessian
    {ι : Type*} (a b : ι → E) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (μ : Measure E) (K : Set E) (ε : ℝ)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      ∀ x ∈ U, u x+q x < 0)
    (hH : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      ∀ x ∈ U, ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform (fun y => u y+q y)) x v v) :
    ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      StrictConvexOn ℝ U (powerTransform (fun y => u y+q y)) := by
  intro q hq hEq
  exact strictConvexOn_of_realHessian_pos hU hconv
    (powerTransform_contDiffOn (hu.add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffOn)
      (hneg q hq hEq)) (hH q hq hEq)

end PowerConvexity
