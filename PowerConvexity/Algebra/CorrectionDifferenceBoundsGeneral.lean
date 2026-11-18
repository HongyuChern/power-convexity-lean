import PowerConvexity.Algebra.CorrectionEntryBoundsGeneral

/-! # Lipschitz bounds for changing the normalized pure Hessian -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem norm_four (a b c d : ℂ) : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  calc
    _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
    _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl

private theorem bound_pow_four {B : ℝ} (hB : 1 ≤ B) : B ≤ B^4 := by
  have hB0 : 0 ≤ B := by linarith
  have h2 : B ≤ B^2 := by nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  have hsq : 1 ≤ B^2 := by nlinarith
  have h22 : B^2 ≤ B^4 := by nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hsq)]
  exact h2.trans h22

theorem modificationAz_difference_bound_general {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (h : ℂ) (g : ι → ℂ) (D C : Matrix ι ι ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hDC : matrixEntryBoundGeneral (D-C) δ) (p : ι) :
    matrixEntryBoundGeneral (modificationAz h g 1 D p-modificationAz h g 1 C p) (B^2*δ) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  have he : (modificationAz h g 1 D p-modificationAz h g 1 C p) i j =
      h*star (g j)*(D i p-C i p) := by simp only [Matrix.sub_apply,modificationAz]; ring
  rw [he,norm_mul,norm_mul,norm_star]
  calc
    _ ≤ B*B*δ := by gcongr <;> first | exact hh | exact hg _ | exact hDC _ _
    _ = _ := by ring

theorem modificationAbar_difference_bound_general {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (h : ℂ) (g : ι → ℂ) (D C : Matrix ι ι ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hDC : matrixEntryBoundGeneral (D-C) δ) (q : ι) :
    matrixEntryBoundGeneral (modificationAbar h g 1 D q-modificationAbar h g 1 C q) (B^2*δ) := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  have he : (modificationAbar h g 1 D q-modificationAbar h g 1 C q) i j =
      h*g i*star (D q j-C q j) := by simp only [Matrix.sub_apply,modificationAbar,star_sub]; ring
  rw [he,norm_mul,norm_mul,norm_star]
  calc
    _ ≤ B*B*δ := by gcongr <;> first | exact hh | exact hg _ | exact hDC _ _
    _ = _ := by ring

theorem modificationASecond_difference_bound_general {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (h : ℂ) (g : ι → ℂ) (D C : Matrix ι ι ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hD : matrixEntryBoundGeneral D 1) (hC : matrixEntryBoundGeneral C 1)
    (hDC : matrixEntryBoundGeneral (D-C) δ) (p q : ι) :
    matrixEntryBoundGeneral (modificationASecond h g 1 D p q-modificationASecond h g 1 C p q) (4*B^4*δ) := by
  have hB0 : 0 ≤ B := by linarith
  have hpow : B*δ ≤ B^4*δ := mul_le_mul_of_nonneg_right (bound_pow_four hB) hδ
  intro i j
  have he : (modificationASecond h g 1 D p q-modificationASecond h g 1 C p q) i j =
      h*(D i p-C i p)*star (D j q)+h*C i p*star (D j q-C j q)+
      h^2*g i*g p*star (D q j-C q j)+h^2*star (g j)*star (g q)*(D i p-C i p) := by
    simp only [Matrix.sub_apply,modificationASecond,star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖h*(D i p-C i p)*star (D j q)‖+‖h*C i p*star (D j q-C j q)‖+
      ‖h^2*g i*g p*star (D q j-C q j)‖+‖h^2*star (g j)*star (g q)*(D i p-C i p)‖ := norm_four _ _ _ _
    _ ≤ B*δ*1+B*1*δ+B^2*B*B*δ+B^2*B*B*δ := by
      simp only [norm_mul,norm_pow,norm_star]
      gcongr <;> first | exact hh | exact hg _ | exact hD _ _ | exact hC _ _ | exact hDC _ _
    _ ≤ _ := by nlinarith

theorem modificationBSecond_difference_bound_general {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (h : ℂ) (g : ι → ℂ) (D C : Matrix ι ι ℂ)
    (hh : ‖h‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B)
    (hDC : matrixEntryBoundGeneral (D-C) δ) (p q : ι) :
    matrixEntryBoundGeneral (modificationBSecond h g 1 D p q-modificationBSecond h g 1 C p q) (4*B^4*δ) := by
  have hB0 : 0 ≤ B := by linarith
  have hpow : B*δ ≤ B^4*δ := mul_le_mul_of_nonneg_right (bound_pow_four hB) hδ
  intro i j
  have he : (modificationBSecond h g 1 D p q-modificationBSecond h g 1 C p q) i j =
      h*(1 : Matrix ι ι ℂ) i q*(D j p-C j p)+
      h*(1 : Matrix ι ι ℂ) j q*(D i p-C i p)+
      h^2*g j*star (g q)*(D i p-C i p)+h^2*g i*star (g q)*(D j p-C j p) := by
    simp only [Matrix.sub_apply,modificationBSecond]
    ring
  rw [he]
  calc
    _ ≤ ‖h*(1 : Matrix ι ι ℂ) i q*(D j p-C j p)‖+
      ‖h*(1 : Matrix ι ι ℂ) j q*(D i p-C i p)‖+
      ‖h^2*g j*star (g q)*(D i p-C i p)‖+‖h^2*g i*star (g q)*(D j p-C j p)‖ := norm_four _ _ _ _
    _ ≤ B*1*δ+B*1*δ+B^2*B*B*δ+B^2*B*B*δ := by
      simp only [norm_mul,norm_pow,norm_star]
      gcongr <;> first | exact hh | exact hg _ | exact matrixEntryBoundGeneral_one _ _ | exact hDC _ _
    _ ≤ _ := by nlinarith

end PowerConvexity
