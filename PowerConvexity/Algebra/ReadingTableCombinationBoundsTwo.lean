import PowerConvexity.Algebra.ReadingTableBoundsTwo
import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # The error in replacing the first Takagi value by one -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PowerConvexity

noncomputable def readingTableCombinationTwo (t : ℝ) (E : Fin 4 → ℂ) : ℂ :=
  E 0+(t:ℂ)^2*E 1-(t:ℂ)*E 2-(t:ℂ)*E 3

private theorem norm_seven (a b c d e f g : ℂ) :
    ‖a+b+c+d+e+f+g‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖+‖g‖ := by
  calc
    _ ≤ ‖a+b+c+d+e+f‖+‖g‖ := norm_add_le _ _
    _ ≤ (‖a+b+c+d+e‖+‖f‖)+‖g‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖a+b+c+d‖+‖e‖)+‖f‖)+‖g‖ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (((‖a+b+c‖+‖d‖)+‖e‖)+‖f‖)+‖g‖ := add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ ((((‖a+b‖+‖c‖)+‖d‖)+‖e‖)+‖f‖)+‖g‖ := add_le_add (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl

theorem readingTableCombinationTwo_difference_bound {t C₀ C₁ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (E F : Fin 4 → ℂ) (hD : ∀ k, ‖E k-F k‖ ≤ C₀*(1-t))
    (hF : ∀ k, ‖F k‖ ≤ C₁) :
    ‖readingTableCombinationTwo t E-readingTableCombinationTwo 1 F‖ ≤
      (4*C₀+4*C₁)*(1-t) := by
  have hδ : 0 ≤ 1-t := by linarith
  have ht2 : t^2 ≤ 1 := by nlinarith [mul_nonneg ht0 hδ]
  have htN : ‖(t:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,abs_of_nonneg ht0] using ht1
  have ht2N : ‖(t:ℂ)^2‖ ≤ 1 := by
    simpa [norm_pow,Complex.norm_real,abs_of_nonneg ht0] using ht2
  have hmN : ‖(t:ℂ)-1‖ = 1-t := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : t-1 ≤ 0)]
    ring
  have hsN : ‖(t:ℂ)^2-1‖ ≤ 2*(1-t) := by
    rw [show (t:ℂ)^2-1 = ((t^2-1:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : t^2-1 ≤ 0)]
    nlinarith [sq_nonneg (1-t)]
  have he : readingTableCombinationTwo t E-readingTableCombinationTwo 1 F =
      (E 0-F 0)+(t:ℂ)^2*(E 1-F 1)+((t:ℂ)^2-1)*F 1+
      (-(t:ℂ)*(E 2-F 2))+(-((t:ℂ)-1)*F 2)+
      (-(t:ℂ)*(E 3-F 3))+(-((t:ℂ)-1)*F 3) := by
    simp only [readingTableCombinationTwo,Complex.ofReal_one]
    ring
  rw [he]
  calc
    _ ≤ ‖E 0-F 0‖+‖(t:ℂ)^2*(E 1-F 1)‖+‖((t:ℂ)^2-1)*F 1‖+
      ‖-(t:ℂ)*(E 2-F 2)‖+‖-((t:ℂ)-1)*F 2‖+
      ‖-(t:ℂ)*(E 3-F 3)‖+‖-((t:ℂ)-1)*F 3‖ := norm_seven _ _ _ _ _ _ _
    _ ≤ C₀*(1-t)+1*(C₀*(1-t))+(2*(1-t))*C₁+
      1*(C₀*(1-t))+(1-t)*C₁+1*(C₀*(1-t))+(1-t)*C₁ := by
      simp only [norm_mul,norm_neg]
      gcongr <;> first | exact hD _ | exact hF _ | exact htN | exact ht2N | exact hsN | exact hmN.le
    _ = _ := by ring

theorem diagonalTwo_entry_bound_unit {t b : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    matrixEntryBoundTwo (Matrix.diagonal ![(t:ℂ),(b:ℂ)]) 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply,Complex.norm_real,abs_of_nonneg ht0,abs_of_nonneg hb0,ht1,hb1]

theorem diagonalTwo_difference_from_one {t b : ℝ} (ht1 : t ≤ 1) :
    matrixEntryBoundTwo
      (Matrix.diagonal ![(t:ℂ),(b:ℂ)]-Matrix.diagonal ![(1:ℂ),(b:ℂ)]) (1-t) := by
  have hn : ‖(t:ℂ)-1‖ = 1-t := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : t-1 ≤ 0)]
    ring
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply,Matrix.sub_apply,hn,sub_nonneg.mpr ht1]

theorem readingTableCombinationTwo_takagi_error {B t b σ : ℝ}
    (hB : 1 ≤ B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hσ : σ = 1-t^2)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (h : ℂ) (g : Fin 2 → ℂ)
    (XB XH YC YH : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : matrixEntryBoundTwo G B) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hXB : ∀ q, matrixEntryBoundTwo (XB q) B) (hXH : ∀ q, matrixEntryBoundTwo (XH q) B)
    (hYC : ∀ p, matrixEntryBoundTwo (YC p) B) (hYH : ∀ p, matrixEntryBoundTwo (YH p) B) :
    ‖readingTableCombinationTwo t (fun k =>
        readingTableResidualsTwo G h g (Matrix.diagonal ![(t:ℂ),(b:ℂ)]) XB XH YC YH k 0 0)-
      readingTableCombinationTwo 1 (fun k =>
        readingTableResidualsTwo G h g (Matrix.diagonal ![(1:ℂ),(b:ℂ)]) XB XH YC YH k 0 0)‖
      ≤ 768*B^5*σ := by
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨hδ,hδσ,hσ0⟩ := one_sub_takagi_le_sigma ht0 ht1 hσ
  have hD := diagonalTwo_entry_bound_unit ht0 ht1 hb0 hb1
  have hC := diagonalTwo_entry_bound_unit (by norm_num : (0:ℝ) ≤ 1) le_rfl hb0 hb1
  have hDC := diagonalTwo_difference_from_one (b := b) ht1
  have hdiff (k : Fin 4) := readingTableResidualsTwo_difference_bound hB hδ G h g _ _ XB XH YC YH
    hG hh hg hD hC hDC hXB hXH hYC hYH k 0 0
  have hbase (k : Fin 4) := readingTableResidualsTwo_entry_bound hB G h g _ XB XH YC YH
    hG hh hg hC hXB hXH hYC hYH k 0 0
  have he := readingTableCombinationTwo_difference_bound ht0 ht1
    (by positivity : 0 ≤ 64*B^5) (by positivity : 0 ≤ 128*B^5) _ _ hdiff hbase
  calc
    _ ≤ (4*(64*B^5)+4*(128*B^5))*(1-t) := he
    _ = 768*B^5*(1-t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hδσ (by positivity)

end PowerConvexity
