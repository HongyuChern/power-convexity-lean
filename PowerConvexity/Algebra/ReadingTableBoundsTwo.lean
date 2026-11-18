import PowerConvexity.Algebra.CorrectionDifferenceBoundsTwo
import PowerConvexity.Algebra.ResidualEntryBoundsTwo

/-! # Uniform and difference bounds for all four rows of ReadingTable

The original third derivatives remain fixed when the normalized pure Hessian
changes. This family is algebraic; it does not assert the existence of a
solution having the changed Hessian.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity

noncomputable def readingTableResidualsTwo (G : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ℂ) (g : Fin 2 → ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (XB XH YC YH : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  let PB := modificationBbar h g 1
  let PH := fun q => (modificationAz h g 1 D q).map star
  let QC := fun p => (PB p).map star
  let QH := fun p => (modificationAbar h g 1 D p).map star
  let SA := modificationASecond h g 1 D
  let SH := fun p q => (SA q p).map star
  let SB := modificationBSecond h g 1 D
  let SC := fun p q => (SB q p).map star
  ![residualEvaluation G (G.map star) 1 XB YC PB QC SA,
    residualEvaluation G (G.map star) 1 XH YH PH QH SH,
    residualEvaluation G (G.map star) 1 XB YH PB QH SB,
    residualEvaluation G (G.map star) 1 XH YC PH QC SC]

theorem matrixEntryBoundTwo_map_star_sub {A C : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ}
    (h : matrixEntryBoundTwo (A-C) B) :
    matrixEntryBoundTwo (A.map star-C.map star) B := by
  intro i j
  simpa only [Matrix.sub_apply,Matrix.map_apply,← star_sub,norm_star] using h i j

theorem readingTableResidualsTwo_entry_bound {B : ℝ} (hB : 1 ≤ B)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (h : ℂ) (g : Fin 2 → ℂ)
    (D : Matrix (Fin 2) (Fin 2) ℂ)
    (XB XH YC YH : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : matrixEntryBoundTwo G B) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hD : matrixEntryBoundTwo D 1)
    (hXB : ∀ q, matrixEntryBoundTwo (XB q) B) (hXH : ∀ q, matrixEntryBoundTwo (XH q) B)
    (hYC : ∀ p, matrixEntryBoundTwo (YC p) B) (hYH : ∀ p, matrixEntryBoundTwo (YH p) B)
    (k : Fin 4) : matrixEntryBoundTwo (readingTableResidualsTwo G h g D XB XH YC YH k) (128*B^5) := by
  have hPB := modificationBbar_entry_bound_two hB h g hh hg
  have hPH := fun q => matrixEntryBoundTwo_map_star (modificationAz_entry_bound_two hB h g D hh hg hD q)
  have hQC := fun p => matrixEntryBoundTwo_map_star (hPB p)
  have hQH := fun p => matrixEntryBoundTwo_map_star (modificationAbar_entry_bound_two hB h g D hh hg hD p)
  have hSA := modificationASecond_entry_bound_two hB h g D hh hg hD
  have hSH := fun p q => matrixEntryBoundTwo_map_star (hSA q p)
  have hSB := modificationBSecond_entry_bound_two hB h g D hh hg hD
  have hSC := fun p q => matrixEntryBoundTwo_map_star (hSB q p)
  fin_cases k
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_entry_bound_two hB G XB YC _ _ _ hG hXB hYC hPB hQC hSA
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_entry_bound_two hB G XH YH _ _ _ hG hXH hYH hPH hQH hSH
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_entry_bound_two hB G XB YH _ _ _ hG hXB hYH hPB hQH hSB
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_entry_bound_two hB G XH YC _ _ _ hG hXH hYC hPH hQC hSC

theorem readingTableResidualsTwo_difference_bound {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (h : ℂ) (g : Fin 2 → ℂ)
    (D C : Matrix (Fin 2) (Fin 2) ℂ)
    (XB XH YC YH : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : matrixEntryBoundTwo G B) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hD : matrixEntryBoundTwo D 1) (hC : matrixEntryBoundTwo C 1)
    (hDC : matrixEntryBoundTwo (D-C) δ)
    (hXB : ∀ q, matrixEntryBoundTwo (XB q) B) (hXH : ∀ q, matrixEntryBoundTwo (XH q) B)
    (hYC : ∀ p, matrixEntryBoundTwo (YC p) B) (hYH : ∀ p, matrixEntryBoundTwo (YH p) B)
    (k : Fin 4) : matrixEntryBoundTwo
      (readingTableResidualsTwo G h g D XB XH YC YH k-
        readingTableResidualsTwo G h g C XB XH YC YH k) (64*B^5*δ) := by
  have hPB := modificationBbar_entry_bound_two hB h g hh hg
  have hPH := fun q => matrixEntryBoundTwo_map_star (modificationAz_entry_bound_two hB h g C hh hg hC q)
  have hQC := fun p => matrixEntryBoundTwo_map_star (hPB p)
  have hQH := fun p => matrixEntryBoundTwo_map_star (modificationAbar_entry_bound_two hB h g D hh hg hD p)
  have hDPB (q : Fin 2) : matrixEntryBoundTwo
      (modificationBbar h g 1 q-modificationBbar h g 1 q) (B^2*δ) := by
    rw [sub_self]; exact matrixEntryBoundTwo_zero (by positivity)
  have hDPH := fun q => matrixEntryBoundTwo_map_star_sub
    (modificationAz_difference_bound_two hB hδ h g D C hh hg hDC q)
  have hDQC := fun p => matrixEntryBoundTwo_map_star_sub (hDPB p)
  have hDQH := fun p => matrixEntryBoundTwo_map_star_sub
    (modificationAbar_difference_bound_two hB hδ h g D C hh hg hDC p)
  have hDSA := modificationASecond_difference_bound_two hB hδ h g D C hh hg hD hC hDC
  have hDSH := fun p q => matrixEntryBoundTwo_map_star_sub (hDSA q p)
  have hDSB := modificationBSecond_difference_bound_two hB hδ h g D C hh hg hDC
  have hDSC := fun p q => matrixEntryBoundTwo_map_star_sub (hDSB q p)
  fin_cases k
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_difference_entry_bound_two hB hδ G (G.map star) XB YC _ _ _ _ _ _
        hG hXB hYC hPB hQC hDPB hDQC hDSA
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_difference_entry_bound_two hB hδ G (G.map star) XH YH _ _ _ _ _ _
        hG hXH hYH hPH hQH hDPH hDQH hDSH
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_difference_entry_bound_two hB hδ G (G.map star) XB YH _ _ _ _ _ _
        hG hXB hYH hPB hQH hDPB hDQH hDSB
  · simpa [readingTableResidualsTwo] using
      residualEvaluation_difference_entry_bound_two hB hδ G (G.map star) XH YC _ _ _ _ _ _
        hG hXH hYC hPH hQC hDPH hDQC hDSC

end PowerConvexity
