import PowerConvexity.Calculus.VariableDensityIsometricCofactorTwo
import PowerConvexity.Calculus.ContinuationUniformClosureC2Two

/-! # One cofactor ellipticity ratio for every actual auxiliary solution on the fixed domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cucfRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cucfRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_uniform_cofactor_ellipticity_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ L : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
      (∀ i, L (realDirections i) = e i) ∧
      (∀ i, L (imagDirections i) = Complex.I • e i) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
        ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
          (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u →
        ∃ B : DeGiorgi.NormalizedEllipticCoeff (2+2) (L ⁻¹' U), B.1.Λ = Λ ∧
          ∀ x ∈ L ⁻¹' U, B.1.a x = c⁻¹ • complexCofactorCoeff (fun y => u (L y)) x := by
  obtain ⟨M,hM,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨L,hLa,hLb,c,hc,Λ,hΛ,hcoeff⟩ :=
    exists_uniform_isometric_variable_density_cofactor_coefficients_two e hab M
  refine ⟨L,hLa,hLb,c,hc,Λ,hΛ,?_⟩
  intro s hs u hdata
  obtain ⟨J⟩ := hdata.2.1
  apply hcoeff U hU u hdata.1
  · intro x hx
    rw [hdata.2.2.2.1 x hx,Complex.ofReal_re]
    exact (dirichletContinuationDensityTwo_bounds e (fun j => Complex.I • e j) hs
      (hwd x (subset_closure hx))).1
  · exact hdata.2.2.1
  · intro x hx
    simpa only [J.hessian_eq hx,realHessian] using
      (hbound s hs u hdata J x (subset_closure hx)).2.2

end PowerConvexity
