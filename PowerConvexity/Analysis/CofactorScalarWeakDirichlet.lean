import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Analysis.ScalarWeakDirichlet

/-! # Actual cofactor weak Dirichlet solvability for scalar L2 loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Matrix Metric MeasureTheory Filter
open scoped BigOperators ComplexOrder ContDiff
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {n : ℕ}
local notation "E" => AmbientSpace (n+n)

theorem variable_density_cofactor_scalar_weak_dirichlet_exists [NeZero (n+n)]
    (hd : 2 ≤ n+n) (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ U : Set E, ∀ hU : IsOpen U, ∀ hbounded : Bornology.IsBounded U,
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∃ B : NormalizedEllipticCoeff (n+n) U, B.1.Λ = Λ ∧
        (∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x) ∧
        ∀ f : E → ℝ, MemLp f 2 (volume.restrict U) →
        ∃ h : E → ℝ,
          IsWeakSolution ⟨U,hU,hbounded,B.1,(fun phi => ∫ x in U, f x*phi x)⟩ h ∧
          ∀ k : E → ℝ,
            IsWeakSolution ⟨U,hU,hbounded,B.1,(fun phi => ∫ x in U, f x*phi x)⟩ k →
            h =ᵐ[volume.restrict U] k := by
  obtain ⟨c,hc,Λ,hΛ,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := n) M
  refine ⟨c,hc,Λ,hΛ,?_⟩
  intro U hU hbounded u hu hdet hpsh hH
  obtain ⟨B,hBΛ,hB⟩ := hcoeff U hU u hu hdet hpsh hH
  refine ⟨B,hBΛ,hB,?_⟩
  intro f hf
  exact scalar_weak_dirichlet_exists hd hU hbounded B.1 hf

end PowerConvexity
