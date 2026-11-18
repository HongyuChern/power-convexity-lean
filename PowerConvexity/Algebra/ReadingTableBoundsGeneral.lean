import PowerConvexity.Algebra.CorrectionDifferenceBoundsGeneral
import PowerConvexity.Algebra.ResidualEntryBoundsGeneral

/-! # Uniform and difference bounds for all four rows of ReadingTable

The original third derivatives remain fixed when the normalized pure Hessian
changes. This family is algebraic; it does not assert the existence of a
solution having the changed Hessian.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def readingTableResidualsGeneral (G : Matrix ι ι ℂ)
    (h : ℂ) (g : ι → ℂ) (D : Matrix ι ι ℂ)
    (XB XH YC YH : ι → Matrix ι ι ℂ) :
    Fin 4 → Matrix ι ι ℂ :=
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

theorem matrixEntryBoundGeneral_map_star_sub {A C : Matrix ι ι ℂ} {B : ℝ}
    (h : matrixEntryBoundGeneral (A-C) B) :
    matrixEntryBoundGeneral (A.map star-C.map star) B := by
  intro i j
  simpa only [Matrix.sub_apply,Matrix.map_apply,← star_sub,norm_star] using h i j

theorem readingTableResidualsGeneral_entry_bound {B : ℝ} (hB : 1 ≤ B)
    (G : Matrix ι ι ℂ) (h : ℂ) (g : ι → ℂ)
    (D : Matrix ι ι ℂ)
    (XB XH YC YH : ι → Matrix ι ι ℂ)
    (hG : matrixEntryBoundGeneral G B) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hD : matrixEntryBoundGeneral D 1)
    (hXB : ∀ q, matrixEntryBoundGeneral (XB q) B) (hXH : ∀ q, matrixEntryBoundGeneral (XH q) B)
    (hYC : ∀ p, matrixEntryBoundGeneral (YC p) B) (hYH : ∀ p, matrixEntryBoundGeneral (YH p) B)
    (k : Fin 4) : matrixEntryBoundGeneral (readingTableResidualsGeneral G h g D XB XH YC YH k) ((Fintype.card ι : ℝ)^2*(2*(Fintype.card ι : ℝ)^2+8*(Fintype.card ι : ℝ)+8)*B^5) := by
  have hPB := modificationBbar_entry_bound_general hB h g hh hg
  have hPH := fun q => matrixEntryBoundGeneral_map_star (modificationAz_entry_bound_general hB h g D hh hg hD q)
  have hQC := fun p => matrixEntryBoundGeneral_map_star (hPB p)
  have hQH := fun p => matrixEntryBoundGeneral_map_star (modificationAbar_entry_bound_general hB h g D hh hg hD p)
  have hSA := modificationASecond_entry_bound_general hB h g D hh hg hD
  have hSH := fun p q => matrixEntryBoundGeneral_map_star (hSA q p)
  have hSB := modificationBSecond_entry_bound_general hB h g D hh hg hD
  have hSC := fun p q => matrixEntryBoundGeneral_map_star (hSB q p)
  fin_cases k
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_entry_bound_general hB G XB YC _ _ _ hG hXB hYC hPB hQC hSA
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_entry_bound_general hB G XH YH _ _ _ hG hXH hYH hPH hQH hSH
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_entry_bound_general hB G XB YH _ _ _ hG hXB hYH hPB hQH hSB
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_entry_bound_general hB G XH YC _ _ _ hG hXH hYC hPH hQC hSC

theorem readingTableResidualsGeneral_difference_bound {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (G : Matrix ι ι ℂ) (h : ℂ) (g : ι → ℂ)
    (D C : Matrix ι ι ℂ)
    (XB XH YC YH : ι → Matrix ι ι ℂ)
    (hG : matrixEntryBoundGeneral G B) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hD : matrixEntryBoundGeneral D 1) (hC : matrixEntryBoundGeneral C 1)
    (hDC : matrixEntryBoundGeneral (D-C) δ)
    (hXB : ∀ q, matrixEntryBoundGeneral (XB q) B) (hXH : ∀ q, matrixEntryBoundGeneral (XH q) B)
    (hYC : ∀ p, matrixEntryBoundGeneral (YC p) B) (hYH : ∀ p, matrixEntryBoundGeneral (YH p) B)
    (k : Fin 4) : matrixEntryBoundGeneral
      (readingTableResidualsGeneral G h g D XB XH YC YH k-
        readingTableResidualsGeneral G h g C XB XH YC YH k) ((Fintype.card ι : ℝ)^2*(4+6*(Fintype.card ι : ℝ))*B^5*δ) := by
  have hPB := modificationBbar_entry_bound_general hB h g hh hg
  have hPH := fun q => matrixEntryBoundGeneral_map_star (modificationAz_entry_bound_general hB h g C hh hg hC q)
  have hQC := fun p => matrixEntryBoundGeneral_map_star (hPB p)
  have hQH := fun p => matrixEntryBoundGeneral_map_star (modificationAbar_entry_bound_general hB h g D hh hg hD p)
  have hDPB (q : ι) : matrixEntryBoundGeneral
      (modificationBbar h g 1 q-modificationBbar h g 1 q) (B^2*δ) := by
    rw [sub_self]; exact matrixEntryBoundGeneral_zero (by positivity)
  have hDPH := fun q => matrixEntryBoundGeneral_map_star_sub
    (modificationAz_difference_bound_general hB hδ h g D C hh hg hDC q)
  have hDQC := fun p => matrixEntryBoundGeneral_map_star_sub (hDPB p)
  have hDQH := fun p => matrixEntryBoundGeneral_map_star_sub
    (modificationAbar_difference_bound_general hB hδ h g D C hh hg hDC p)
  have hDSA := modificationASecond_difference_bound_general hB hδ h g D C hh hg hD hC hDC
  have hDSH := fun p q => matrixEntryBoundGeneral_map_star_sub (hDSA q p)
  have hDSB := modificationBSecond_difference_bound_general hB hδ h g D C hh hg hDC
  have hDSC := fun p q => matrixEntryBoundGeneral_map_star_sub (hDSB q p)
  fin_cases k
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_difference_entry_bound_general hB hδ G (G.map star) XB YC _ _ _ _ _ _
        hG hXB hYC hPB hQC hDPB hDQC hDSA
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_difference_entry_bound_general hB hδ G (G.map star) XH YH _ _ _ _ _ _
        hG hXH hYH hPH hQH hDPH hDQH hDSH
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_difference_entry_bound_general hB hδ G (G.map star) XB YH _ _ _ _ _ _
        hG hXB hYH hPB hQH hDPB hDQH hDSB
  · simpa [readingTableResidualsGeneral] using
      residualEvaluation_difference_entry_bound_general hB hδ G (G.map star) XH YC _ _ _ _ _ _
        hG hXH hYC hPH hQC hDPH hDQC hDSC

end PowerConvexity
