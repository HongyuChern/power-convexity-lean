import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

/-! # Actual weak Dirichlet solutions for the cofactor operator.
The coefficients and ellipticity constants are constructed from the actual
potential. The solution has zero Sobolev trace and satisfies the equation
against every H01 test and every weak-gradient witness. No classical boundary
value, C2 closure jet or classical inverse is asserted.
-/
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

theorem variable_density_cofactor_weak_dirichlet_exists [NeZero (n+n)]
    (hd : 2 ≤ n+n) (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ U : Set E, ∀ hU : IsOpen U, ∀ hbounded : Bornology.IsBounded U,
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∃ B : NormalizedEllipticCoeff (n+n) U, B.1.Λ = Λ ∧
        (∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x) ∧
        ∀ F : E → E, MemLp F 2 (volume.restrict U) →
        ∃ h : E → ℝ,
          IsWeakSolution ⟨U,hU,hbounded,B.1,weakProblemRHSOfField (Ω := U) F⟩ h ∧
          ∀ k : E → ℝ,
            IsWeakSolution ⟨U,hU,hbounded,B.1,weakProblemRHSOfField (Ω := U) F⟩ k →
            h =ᵐ[volume.restrict U] k := by
  obtain ⟨c,hc,Λ,hΛ,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := n) M
  refine ⟨c,hc,Λ,hΛ,?_⟩
  intro U hU hbounded u hu hdet hpsh hH
  obtain ⟨B,hBΛ,hB⟩ := hcoeff U hU u hu hdet hpsh hH
  refine ⟨B,hBΛ,hB,?_⟩
  intro F hF
  obtain ⟨h,hh⟩ := weakProblem_exists_of_divergenceData hd hU hbounded B.1 hF
  exact ⟨h,hh,fun k hk => weakProblem_unique hd hh hk⟩

theorem actual_weak_dirichlet_all_test_identity
    {d : ℕ} [NeZero d] {P : WeakProblem (d := d)}
    {F : AmbientSpace d → AmbientSpace d}
    (hR : P.rhs = weakProblemRHSOfField (Ω := P.Ω) F)
    {h : AmbientSpace d → ℝ} (hh : IsWeakSolution P h) :
    MemH01 h P.Ω ∧ ∀ hw : MemW1pWitness 2 h P.Ω,
      ∀ phi : AmbientSpace d → ℝ, MemH01 phi P.Ω →
      ∀ hphi : MemW1pWitness 2 phi P.Ω,
        bilinFormOfCoeff P.coeff hw hphi = divergenceRHSOfField F hphi := by
  refine ⟨hh.1,?_⟩
  intro hw phi hphi0 hphi
  rw [hh.2 hw phi hphi0 hphi,hR]
  exact weakProblemRHSOfField_eq_of_memH01 P.hΩ hphi0 hphi

end PowerConvexity
