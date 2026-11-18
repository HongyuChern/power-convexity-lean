import PowerConvexity.Algebra.WeightedSquares

/-! # Quantitative scalar bounds for the retained contact defects -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity

theorem one_sub_takagi_le_sigma {b σ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hσ : σ = 1-b^2) : 0 ≤ 1-b ∧ 1-b ≤ σ ∧ 0 ≤ σ := by
  have hb : 0 ≤ b*(1-b) := mul_nonneg hb0 (sub_nonneg.mpr hb1)
  constructor
  · linarith
  constructor <;> nlinarith

theorem first_column_defect_norm_bound {b σ B : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hσ : σ = 1-b^2) (hB : 0 ≤ B) (D R S A e : ℂ)
    (hD : ‖D‖ ≤ B) (hR : ‖R‖ ≤ B) (hA : ‖A‖ ≤ B)
    (he : e = (1-(b:ℂ))*(D+R)-S-(σ:ℂ)*A) :
    ‖e‖ ≤ 3*B*σ+‖S‖ := by
  obtain ⟨hb,hbσ,hσ0⟩ := one_sub_takagi_le_sigma hb0 hb1 hσ
  have hbn : ‖1-(b:ℂ)‖ = 1-b := by
    rw [show 1-(b:ℂ) = ((1-b:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  have hσn : ‖(σ:ℂ)‖ = σ := by simp [Complex.norm_real,abs_of_nonneg hσ0]
  rw [he]
  calc
    _ ≤ ‖(1-(b:ℂ))*(D+R)-S‖+‖(σ:ℂ)*A‖ := norm_sub_le _ _
    _ ≤ (‖(1-(b:ℂ))*(D+R)‖+‖S‖)+‖(σ:ℂ)*A‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = (1-b)*‖D+R‖+‖S‖+σ*‖A‖ := by rw [norm_mul,norm_mul,hbn,hσn]
    _ ≤ σ*(B+B)+‖S‖+σ*B := by
      gcongr
      exact (norm_add_le D R).trans (add_le_add hD hR)
    _ = _ := by ring

theorem weightedSquare_sub_norm_le_two (G : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℂ) {M B ε : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ p q, ‖G q p‖ ≤ M) (hv : ∀ p, ‖v p‖ ≤ B) (hw : ∀ p, ‖w p‖ ≤ B)
    (hd : ∀ p, ‖v p-w p‖ ≤ ε) :
    ‖weightedSquare G v-weightedSquare G w‖ ≤ 8*M*B*ε := by
  have he : weightedSquare G v-weightedSquare G w =
      ∑ p,∑ q,G q p*((v p-w p)*star (v q)+w p*star (v q-w q)) := by
    simp [weightedSquare,Fin.sum_univ_two,star_sub]
    ring
  have hb (p q : Fin 2) : ‖G q p*((v p-w p)*star (v q)+w p*star (v q-w q))‖ ≤ 2*M*B*ε := by
    rw [norm_mul]
    calc
      _ ≤ M*(‖(v p-w p)*star (v q)‖+‖w p*star (v q-w q)‖) := by
        gcongr
        · exact hG p q
        · exact norm_add_le _ _
      _ = M*(‖v p-w p‖*‖v q‖+‖w p‖*‖v q-w q‖) := by simp only [norm_mul,norm_star]
      _ ≤ M*(ε*B+B*ε) := by gcongr <;> first | exact hd _ | exact hv _ | exact hw _
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ∑ p,‖∑ q,G q p*((v p-w p)*star (v q)+w p*star (v q-w q))‖ := norm_sum_le _ _
    _ ≤ ∑ p,∑ q,‖G q p*((v p-w p)*star (v q)+w p*star (v q-w q))‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_sum_le _ _
    _ ≤ ∑ _p : Fin 2,∑ _q : Fin 2,2*M*B*ε := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      exact hb p q
    _ = _ := by simp [Fin.sum_univ_two]; ring

end PowerConvexity
