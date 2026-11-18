import PowerConvexity.Algebra.MatrixEntryBoundsTwo

/-! # Explicit entry bounds for the actual algebraic Hessian corrections -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity

private theorem norm_add_four_le (a b c d : ℂ) :
    ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  calc
    _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
    _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl

private theorem norm_add_seven_le (a b c d e f g : ℂ) :
    ‖a+b+c+d+e+f+g‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖+‖g‖ := by
  exact (norm_add_four_le (a+b+c+d) e f g).trans
    (add_le_add (add_le_add (add_le_add (norm_add_four_le a b c d) le_rfl) le_rfl) le_rfl)

private theorem self_le_pow_four {B : ℝ} (hB : 1 ≤ B) : B ≤ B^4 := by
  have hB0 : 0 ≤ B := by linarith
  have h2 : B ≤ B^2 := by nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  have h22 : B^2 ≤ B^4 := by
    have hsq : 1 ≤ B^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hsq)]
  exact h2.trans h22

theorem modificationAz_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (h : ℂ) (g : Fin 2 → ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) (hD : matrixEntryBoundTwo D 1) (p : Fin 2) :
    matrixEntryBoundTwo (modificationAz h g 1 D p) (2*B^2) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  unfold modificationAz
  calc
    _ ≤ ‖h*star (g j)*D i p‖+‖h*g i*(1 : Matrix (Fin 2) (Fin 2) ℂ) p j‖ := norm_add_le _ _
    _ = ‖h‖*‖g j‖*‖D i p‖+‖h‖*‖g i‖*‖(1 : Matrix (Fin 2) (Fin 2) ℂ) p j‖ := by simp only [norm_mul,norm_star]
    _ ≤ B*B*1+B*B*1 := by gcongr <;> first | exact hh | exact hg _ | exact hD _ _ | exact matrixEntryBoundTwo_one _ _
    _ = _ := by ring

theorem modificationAbar_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (h : ℂ) (g : Fin 2 → ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) (hD : matrixEntryBoundTwo D 1) (q : Fin 2) :
    matrixEntryBoundTwo (modificationAbar h g 1 D q) (2*B^2) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  unfold modificationAbar
  calc
    _ ≤ ‖h*star (g j)*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+‖h*g i*star (D q j)‖ := norm_add_le _ _
    _ = ‖h‖*‖g j‖*‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+‖h‖*‖g i‖*‖D q j‖ := by simp only [norm_mul,norm_star]
    _ ≤ B*B*1+B*B*1 := by gcongr <;> first | exact hh | exact hg _ | exact hD _ _ | exact matrixEntryBoundTwo_one _ _
    _ = _ := by ring

theorem modificationBbar_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (h : ℂ) (g : Fin 2 → ℂ) (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) (q : Fin 2) :
    matrixEntryBoundTwo (modificationBbar h g 1 q) (2*B^2) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  unfold modificationBbar
  calc
    _ ≤ ‖h*g j*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+‖h*g i*(1 : Matrix (Fin 2) (Fin 2) ℂ) j q‖ := norm_add_le _ _
    _ = ‖h‖*‖g j‖*‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+‖h‖*‖g i‖*‖(1 : Matrix (Fin 2) (Fin 2) ℂ) j q‖ := by simp only [norm_mul]
    _ ≤ B*B*1+B*B*1 := by gcongr <;> first | exact hh | exact hg _ | exact matrixEntryBoundTwo_one _ _
    _ = _ := by ring

theorem modificationASecond_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (h : ℂ) (g : Fin 2 → ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) (hD : matrixEntryBoundTwo D 1) (p q : Fin 2) :
    matrixEntryBoundTwo (modificationASecond h g 1 D p q) (8*B^4) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  unfold modificationASecond
  calc
    _ ≤ ‖h*D i p*star (D j q)‖+‖h*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q*(1 : Matrix (Fin 2) (Fin 2) ℂ) p j‖+
      ‖h^2*g p*star (g j)*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+
      ‖2*h^2*g i*star (g j)*(1 : Matrix (Fin 2) (Fin 2) ℂ) p q‖+
      ‖h^2*g i*g p*star (D q j)‖+‖h^2*star (g j)*star (g q)*D i p‖+
      ‖h^2*g i*star (g q)*(1 : Matrix (Fin 2) (Fin 2) ℂ) p j‖ := norm_add_seven_le _ _ _ _ _ _ _
    _ ≤ B*1*1+B*1*1+B^2*B*B*1+2*B^2*B*B*1+B^2*B*B*1+B^2*B*B*1+B^2*B*B*1 := by
      simp only [norm_mul,norm_pow,norm_star]
      norm_num only [Complex.norm_ofNat]
      gcongr <;> first | exact hh | exact hg _ | exact hD _ _ | exact matrixEntryBoundTwo_one _ _
    _ ≤ 8*B^4 := by nlinarith [self_le_pow_four hB]

theorem modificationBSecond_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (h : ℂ) (g : Fin 2 → ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B) (hD : matrixEntryBoundTwo D 1) (p q : Fin 2) :
    matrixEntryBoundTwo (modificationBSecond h g 1 D p q) (8*B^4) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  unfold modificationBSecond
  calc
    _ ≤ ‖h*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q*D j p‖+‖h*(1 : Matrix (Fin 2) (Fin 2) ℂ) j q*D i p‖+
      ‖h^2*g p*g j*(1 : Matrix (Fin 2) (Fin 2) ℂ) i q‖+
      ‖h^2*g i*g p*(1 : Matrix (Fin 2) (Fin 2) ℂ) j q‖+
      ‖2*h^2*g i*g j*(1 : Matrix (Fin 2) (Fin 2) ℂ) p q‖+
      ‖h^2*g j*star (g q)*D i p‖+‖h^2*g i*star (g q)*D j p‖ := norm_add_seven_le _ _ _ _ _ _ _
    _ ≤ B*1*1+B*1*1+B^2*B*B*1+B^2*B*B*1+2*B^2*B*B*1+B^2*B*B*1+B^2*B*B*1 := by
      simp only [norm_mul,norm_pow,norm_star]
      norm_num only [Complex.norm_ofNat]
      gcongr <;> first | exact hh | exact hg _ | exact hD _ _ | exact matrixEntryBoundTwo_one _ _
    _ ≤ 8*B^4 := by nlinarith [self_le_pow_four hB]

end PowerConvexity
