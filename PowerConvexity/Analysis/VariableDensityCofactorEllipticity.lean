import PowerConvexity.Calculus.VariableDensityCofactor

/-! # Uniform normalized cofactor coefficients on the actual variable-density branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Matrix Metric
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n+n)
local notation "W" => Matrix (Fin n) (Fin n) ℂ

theorem exists_uniform_variable_density_cofactor_coefficients [NeZero (n+n)] (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ U : Set E, IsOpen U → ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∃ B : DeGiorgi.NormalizedEllipticCoeff (n+n) U, B.1.Λ = Λ ∧
        ∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x := by
  let S := (fun A : W => realLinearizedWeight A.adjugate) '' complexDetLowerFamily n M
  have hS : IsCompact S := (complexDetLowerFamily_compact M).image
    (continuous_realLinearizedWeight.comp continuous_id.matrix_adjugate)
  have hSne : S.Nonempty := (complexDetLowerFamily_nonempty M).image _
  have hSpos : ∀ A ∈ S, A.PosDef := by
    rintro _ ⟨A,hA,rfl⟩
    exact realLinearizedWeight_posDef (positive_complex_adjugate (complexDetLowerFamily_posDef hA))
  obtain ⟨c,hc,Λ,hΛ,hnormalize⟩ := uniform_local_normalization_of_compact_family hS hSne hSpos
  refine ⟨c,hc,Λ,hΛ,?_⟩
  intro U hU u hu hdet hA hM
  apply hnormalize U hU.measurableSet (complexCofactorCoeff u)
  · intro x hx
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    exact (complexCofactorCoeff_contDiffAt
      (hu.contDiffAt (hU.mem_nhds hx)) i j).continuousAt.continuousWithinAt
  · intro x hx
    exact mem_image_of_mem _ (complexHessian_mem_complexDetLowerFamily
      ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) (hA x hx) (hdet x hx) (hM x hx))

end PowerConvexity
