import PowerConvexity.Algebra.TypeICompletionTwo
import PowerConvexity.Algebra.DimensionTwoCoercive
import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # A full-column defect estimate without a spectral gap -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators ComplexOrder
namespace PowerConvexity

theorem typeI_full_column_defect_bound_two (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    {M B ε : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ p q, ‖rankOneWeightTwo r q p‖ ≤ M)
    (hX : ∀ p s, ‖W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s‖ ≤ B)
    (hD : ∀ p s, ‖D p s‖ ≤ B)
    (hd : ∀ p s, ‖D p s-(W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s)‖ ≤ ε) :
    (typeIQuadraticTwo (rankOneWeightTwo r) W+(Complex.normSq τ:ℂ)*(rankOneWeightTwo r).trace-
      ∑ s,weightedSquare (rankOneWeightTwo r) (fun p => D p s)).re ≤ 16*M*B*ε := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := fun p s => W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s
  let err : ℂ := ∑ s, (weightedSquare (rankOneWeightTwo r) (fun p => X p s)-
    weightedSquare (rankOneWeightTwo r) (fun p => D p s))
  have he : typeIQuadraticTwo (rankOneWeightTwo r) W+(Complex.normSq τ:ℂ)*(rankOneWeightTwo r).trace-
      ∑ s,weightedSquare (rankOneWeightTwo r) (fun p => D p s) =
      (Complex.normSq W.trace:ℂ)-(∑ p,∑ s,(Complex.normSq (W p s):ℂ))+err := by
    have h1 := typeI_rankOne_trace_zero_two W hW r htrace
    have h2 := weightedSquare_column_shift_two (rankOneWeightTwo r) W hW τ
    rw [htrace,mul_zero,add_zero] at h2
    dsimp only [err,X]
    rw [Finset.sum_sub_distrib]
    linear_combination h1-h2
  have hsign := dimensionTwo_skew_sign W hW r htrace
  have hsum : ‖err‖ ≤ 16*M*B*ε := by
    dsimp only [err]
    calc
      _ ≤ ∑ s,‖weightedSquare (rankOneWeightTwo r) (fun p => X p s)-
          weightedSquare (rankOneWeightTwo r) (fun p => D p s)‖ := norm_sum_le _ _
      _ ≤ ∑ _s : Fin 2,8*M*B*ε := by
        apply Finset.sum_le_sum
        intro s _
        apply weightedSquare_sub_norm_le_two _ _ _ hM hB hε hG
          (fun p => hX p s) (fun p => hD p s)
        intro p
        rw [norm_sub_rev]
        exact hd p s
      _ = _ := by simp [Fin.sum_univ_two]; ring
  rw [he]
  simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.re_sum]
  have hr := (Complex.re_le_norm err).trans hsum
  linarith

theorem normalized_full_entry_defect_bound {b c σ τ B g : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hσ : σ = 1-b^2) (hτ : τ = 1-c^2) (hB : 0 ≤ B)
    (D R X Z : ℂ) (hD : ‖D‖ ≤ B) (hR : ‖R‖ ≤ B) (hZ : ‖Z‖ ≤ g)
    (he : Z = X-(c:ℂ)*D+(1-(b:ℂ))*R) :
    ‖D-X‖ ≤ B*(σ+τ)+g := by
  obtain ⟨hb,hbσ,hσ0⟩ := one_sub_takagi_le_sigma hb0 hb1 hσ
  obtain ⟨hc,hcτ,hτ0⟩ := one_sub_takagi_le_sigma hc0 hc1 hτ
  have hbn : ‖1-(b:ℂ)‖ = 1-b := by
    rw [show 1-(b:ℂ) = ((1-b:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  have hcn : ‖1-(c:ℂ)‖ = 1-c := by
    rw [show 1-(c:ℂ) = ((1-c:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  have hEq : D-X = (1-(c:ℂ))*D+(1-(b:ℂ))*R-Z := by linear_combination he
  rw [hEq]
  calc
    _ ≤ ‖(1-(c:ℂ))*D+(1-(b:ℂ))*R‖+‖Z‖ := norm_sub_le _ _
    _ ≤ (‖(1-(c:ℂ))*D‖+‖(1-(b:ℂ))*R‖)+‖Z‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = ((1-c)*‖D‖+(1-b)*‖R‖)+‖Z‖ := by rw [norm_mul,norm_mul,hcn,hbn]
    _ ≤ τ*B+σ*B+g := by gcongr
    _ = _ := by ring

end PowerConvexity
