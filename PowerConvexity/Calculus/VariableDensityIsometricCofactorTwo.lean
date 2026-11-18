import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # One fixed real isometry and uniform actual cofactor coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
local instance vdicRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance vdicRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem exists_uniform_isometric_variable_density_cofactor_coefficients_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j))) (M : ℝ) :
    ∃ L : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
      (∀ i, L (realDirections i) = e i) ∧
      (∀ i, L (imagDirections i) = Complex.I • e i) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
        ∀ U : Set E, IsOpen U → ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
        (∀ x ∈ U, 1 ≤ (complexHessian e (fun j => Complex.I • e j) u x).det.re) →
        (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
        (∀ x ∈ U, ‖realHessian u x‖ ≤ M) →
        ∃ B : DeGiorgi.NormalizedEllipticCoeff (2+2) (L ⁻¹' U), B.1.Λ = Λ ∧
          ∀ x ∈ L ⁻¹' U, B.1.a x = c⁻¹ • complexCofactorCoeff (fun y => u (L y)) x := by
  obtain ⟨L,hLa,hLb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  obtain ⟨c,hc,Λ,hΛ,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := 2) M
  refine ⟨L,hLa,hLb,c,hc,Λ,hΛ,?_⟩
  intro U hU u hu hdet hA hM
  have hreg (x : DeGiorgi.AmbientSpace (2+2)) (hx : x ∈ L ⁻¹' U) :
      ContDiffAt ℝ 2 u (L x) := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have heq (x : DeGiorgi.AmbientSpace (2+2)) (hx : x ∈ L ⁻¹' U) :
      complexHessian realDirections imagDirections (fun y => u (L y)) x =
        complexHessian e (fun j => Complex.I • e j) u (L x) := by
    rw [complexHessian_comp_linearIsometry L (hreg x hx)]
    rw [show (fun i => L (realDirections i)) = e from funext hLa,
      show (fun i => L (imagDirections i)) = (fun j => Complex.I • e j) from funext hLb]
  apply hcoeff (L ⁻¹' U) (hU.preimage L.continuous) (fun y => u (L y))
    (hu.comp L.contDiff.contDiffOn (fun _ hx => hx))
  · intro x hx
    rw [heq x hx]
    exact hdet (L x) hx
  · intro x hx
    rw [heq x hx]
    exact hA (L x) hx
  · intro x hx i j
    change |realHessian (fun y => u (L y)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M
    rw [realHessian_comp_linearIsometry L (hreg x hx)]
    have hh := (realHessian u (L x)).le_opNorm₂
      (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))
    simpa only [L.norm_map,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
      hh.trans (by simpa using hM (L x) hx)

end PowerConvexity
