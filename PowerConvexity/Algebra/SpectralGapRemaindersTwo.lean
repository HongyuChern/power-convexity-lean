import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # Exact gap comparison and quantitative inverse-gap error -/
set_option autoImplicit false
namespace PowerConvexity

theorem normalized_gap_relation (b₀ b₁ : ℝ) :
    1-b₁^2 = (b₀^2-b₁^2)+(1-b₀^2) := by ring

theorem inverse_gap_difference {κ μ σ : ℝ} (hκ : 0 < κ) (hσ : 0 ≤ σ)
    (hμ : μ = κ+σ) : 1/κ-1/μ = σ/(κ*μ) := by
  have hμp : 0 < μ := by linarith
  field_simp
  nlinarith

theorem inverse_gap_difference_le {κ μ σ δ : ℝ} (hδ : 0 < δ) (hκ : δ ≤ κ)
    (hσ : 0 ≤ σ) (hμ : μ = κ+σ) :
    0 ≤ 1/κ-1/μ ∧ 1/κ-1/μ ≤ σ/δ^2 := by
  have hκp : 0 < κ := hδ.trans_le hκ
  have hμp : 0 < μ := by linarith
  have hδμ : δ ≤ μ := by linarith
  rw [inverse_gap_difference hκp hσ hμ]
  constructor
  · exact div_nonneg hσ (mul_pos hκp hμp).le
  · apply div_le_div_of_nonneg_left hσ (sq_pos_of_pos hδ)
    simpa only [pow_two] using mul_le_mul hκ hδμ hδ.le hκp.le

theorem normalized_inverse_gap_difference_le {b₀ b₁ δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ b₀^2-b₁^2) (hσ : 0 ≤ 1-b₀^2) :
    0 ≤ 1/(b₀^2-b₁^2)-1/(1-b₁^2) ∧
    1/(b₀^2-b₁^2)-1/(1-b₁^2) ≤ (1-b₀^2)/δ^2 :=
  inverse_gap_difference_le hδ hgap hσ (normalized_gap_relation b₀ b₁)

end PowerConvexity
