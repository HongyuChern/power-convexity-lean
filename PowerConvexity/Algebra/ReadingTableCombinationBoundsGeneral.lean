import PowerConvexity.Algebra.ReadingTableBoundsGeneral
import PowerConvexity.Algebra.ReadingTableCombinationBoundsTwo

/-! # General-dimensional ReadingTable error at a selected Takagi index -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def readingTableErrorCoefficientGeneral (n : ℕ) : ℝ :=
  4*((n : ℝ)^2*(4+6*(n : ℝ)))+4*((n : ℝ)^2*(2*(n : ℝ)^2+8*(n : ℝ)+8))

theorem diagonal_entry_bound_unit_general (d : ι → ℝ)
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1) :
    matrixEntryBoundGeneral (Matrix.diagonal (fun j => (d j : ℂ))) 1 := by
  intro j l
  by_cases hjl : j=l
  · subst l
    simpa [Matrix.diagonal_apply,Complex.norm_real,abs_of_nonneg (hd0 j)] using hd1 j
  · simp [Matrix.diagonal_apply,hjl]

theorem diagonal_difference_from_one_general (d : ι → ℝ) (i : ι) (hd1 : d i ≤ 1) :
    matrixEntryBoundGeneral
      (Matrix.diagonal (fun j => (d j : ℂ))-
        Matrix.diagonal (fun j => (Function.update d i 1 j : ℂ))) (1-d i) := by
  have hn : ‖(d i : ℂ)-1‖ = 1-d i := by
    rw [show (d i : ℂ)-1 = ((d i-1 : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : d i-1 ≤ 0)]
    ring
  intro j l
  by_cases hjl : j=l
  · subst l
    by_cases hji : j=i
    · subst j
      simpa [Matrix.diagonal_apply,Matrix.sub_apply] using hn.le
    · simp [Matrix.diagonal_apply,Matrix.sub_apply,Function.update_of_ne hji,sub_nonneg.mpr hd1]
  · simp [Matrix.diagonal_apply,Matrix.sub_apply,hjl,sub_nonneg.mpr hd1]

theorem readingTableCombination_takagi_error_general {B σ : ℝ}
    (hB : 1 ≤ B) (d : ι → ℝ) (i : ι)
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1) (hσ : σ = 1-d i^2)
    (G : Matrix ι ι ℂ) (h : ℂ) (g : ι → ℂ)
    (XB XH YC YH : ι → Matrix ι ι ℂ)
    (hG : matrixEntryBoundGeneral G B) (hh : ‖h‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ B)
    (hXB : ∀ q, matrixEntryBoundGeneral (XB q) B) (hXH : ∀ q, matrixEntryBoundGeneral (XH q) B)
    (hYC : ∀ p, matrixEntryBoundGeneral (YC p) B) (hYH : ∀ p, matrixEntryBoundGeneral (YH p) B) :
    ‖readingTableCombinationTwo (d i) (fun k =>
        readingTableResidualsGeneral G h g (Matrix.diagonal (fun j => (d j : ℂ))) XB XH YC YH k i i)-
      readingTableCombinationTwo 1 (fun k =>
        readingTableResidualsGeneral G h g
          (Matrix.diagonal (fun j => (Function.update d i 1 j : ℂ))) XB XH YC YH k i i)‖ ≤
      readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5*σ := by
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨hδ,hδσ,_hσ0⟩ := one_sub_takagi_le_sigma (hd0 i) (hd1 i) hσ
  have hD := diagonal_entry_bound_unit_general d hd0 hd1
  have hc0 : ∀ j, 0 ≤ Function.update d i 1 j := by
    intro j
    by_cases hji : j=i
    · subst j; simp
    · simpa [Function.update_of_ne hji] using hd0 j
  have hc1 : ∀ j, Function.update d i 1 j ≤ 1 := by
    intro j
    by_cases hji : j=i
    · subst j; simp
    · simpa [Function.update_of_ne hji] using hd1 j
  have hC := diagonal_entry_bound_unit_general (Function.update d i 1) hc0 hc1
  have hDC := diagonal_difference_from_one_general d i (hd1 i)
  have hdiff (k : Fin 4) := readingTableResidualsGeneral_difference_bound hB hδ G h g _ _ XB XH YC YH
    hG hh hg hD hC hDC hXB hXH hYC hYH k i i
  have hbase (k : Fin 4) := readingTableResidualsGeneral_entry_bound hB G h g _ XB XH YC YH
    hG hh hg hC hXB hXH hYC hYH k i i
  have he := readingTableCombinationTwo_difference_bound (hd0 i) (hd1 i)
    (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*(4+6*(Fintype.card ι : ℝ))*B^5)
    (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*(2*(Fintype.card ι : ℝ)^2+8*(Fintype.card ι : ℝ)+8)*B^5)
    _ _ hdiff hbase
  calc
    _ ≤ (4*((Fintype.card ι : ℝ)^2*(4+6*(Fintype.card ι : ℝ))*B^5)+
      4*((Fintype.card ι : ℝ)^2*(2*(Fintype.card ι : ℝ)^2+8*(Fintype.card ι : ℝ)+8)*B^5))*(1-d i) := he
    _ = readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5*(1-d i) := by
      unfold readingTableErrorCoefficientGeneral
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hδσ (by unfold readingTableErrorCoefficientGeneral; positivity)

end PowerConvexity
