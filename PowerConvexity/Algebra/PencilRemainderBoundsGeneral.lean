import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # Quantitative finite-dimensional pencil remainders -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace PowerConvexity

theorem pencil_product_defect_le {σ B : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hB : 0 ≤ B)
    (X Y A C : ℂ) (hX : ‖X‖ ≤ B) (hY : ‖Y‖ ≤ B) (hA : ‖A‖ ≤ B) (hC : ‖C‖ ≤ B) :
    ‖(X-(σ : ℂ)*A)*(Y-(σ : ℂ)*C)-X*Y‖ ≤ 3*B^2*σ := by
  have hn : ‖(σ : ℂ)‖ = σ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ0]
  have hP : ‖X-(σ : ℂ)*A‖ ≤ 2*B := by
    calc
      _ ≤ ‖X‖+‖(σ : ℂ)*A‖ := norm_sub_le _ _
      _ ≤ B+σ*B := by rw [norm_mul,hn]; gcongr
      _ ≤ 2*B := by nlinarith
  have he : (X-(σ : ℂ)*A)*(Y-(σ : ℂ)*C)-X*Y =
      -(X-(σ : ℂ)*A)*((σ : ℂ)*C)-((σ : ℂ)*A)*Y := by ring
  rw [he]
  calc
    _ ≤ ‖-(X-(σ : ℂ)*A)*((σ : ℂ)*C)‖+‖((σ : ℂ)*A)*Y‖ := norm_sub_le _ _
    _ = ‖X-(σ : ℂ)*A‖*(σ*‖C‖)+(σ*‖A‖)*‖Y‖ := by simp only [norm_mul,norm_neg,hn]
    _ ≤ (2*B)*(σ*B)+(σ*B)*B := by gcongr
    _ = _ := by ring

theorem pencil_pair_defect_le {σ B : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hB : 0 ≤ B)
    (X Y Z W A C D F : ℂ)
    (hX : ‖X‖ ≤ B) (hY : ‖Y‖ ≤ B) (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B)
    (hA : ‖A‖ ≤ B) (hC : ‖C‖ ≤ B) (hD : ‖D‖ ≤ B) (hF : ‖F‖ ≤ B) :
    ‖(X-(σ : ℂ)*A)*(Y-(σ : ℂ)*C)+(Z-(σ : ℂ)*D)*(W-(σ : ℂ)*F)-(X*Y+Z*W)‖ ≤
      6*B^2*σ := by
  have he : (X-(σ : ℂ)*A)*(Y-(σ : ℂ)*C)+(Z-(σ : ℂ)*D)*(W-(σ : ℂ)*F)-(X*Y+Z*W) =
    ((X-(σ : ℂ)*A)*(Y-(σ : ℂ)*C)-X*Y)+((Z-(σ : ℂ)*D)*(W-(σ : ℂ)*F)-Z*W) := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    (pencil_product_defect_le hσ0 hσ1 hB X Y A C hX hY hA hC)
    (pencil_product_defect_le hσ0 hσ1 hB Z W D F hZ hW hD hF)).trans_eq (by ring))

theorem finite_pencil_second_remainder_bound
    {κ : Type*} [Fintype κ] {σ B δ Gv Gw : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hGv : 0 ≤ Gv) (hGw : 0 ≤ Gw)
    (S T A2 sv sw av aw : ℂ) (X Y Z W A C D F den : κ → ℂ)
    (hA2 : ‖A2‖ ≤ B) (hsv : ‖sv‖ ≤ Gv) (hsw : ‖sw‖ ≤ Gw)
    (hav : ‖av‖ ≤ B) (haw : ‖aw‖ ≤ B)
    (hX : ∀ j, ‖X j‖ ≤ B) (hY : ∀ j, ‖Y j‖ ≤ B)
    (hZ : ∀ j, ‖Z j‖ ≤ B) (hW : ∀ j, ‖W j‖ ≤ B)
    (hA : ∀ j, ‖A j‖ ≤ B) (hC : ∀ j, ‖C j‖ ≤ B)
    (hD : ∀ j, ‖D j‖ ≤ B) (hF : ∀ j, ‖F j‖ ≤ B)
    (hden : ∀ j, δ ≤ ‖den j‖)
    (he : S = T-(σ : ℂ)*A2-sv*aw-sw*av+
      ∑ j, ((X j-(σ : ℂ)*A j)*(Y j-(σ : ℂ)*C j)+
        (Z j-(σ : ℂ)*D j)*(W j-(σ : ℂ)*F j))/den j) :
    ‖S-(T+∑ j, (X j*Y j+Z j*W j)/den j)‖ ≤
      (B+6*(Fintype.card κ : ℝ)*B^2/δ)*σ+B*(Gv+Gw) := by
  have hn : ‖(σ : ℂ)‖ = σ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ0]
  have heq : S-(T+∑ j, (X j*Y j+Z j*W j)/den j) =
      -((σ : ℂ)*A2)-sv*aw-sw*av+
      ∑ j, (((X j-(σ : ℂ)*A j)*(Y j-(σ : ℂ)*C j)+
        (Z j-(σ : ℂ)*D j)*(W j-(σ : ℂ)*F j))-(X j*Y j+Z j*W j))/den j := by
    rw [he]
    simp only [sub_div,Finset.sum_sub_distrib]
    ring
  have hs : ‖∑ j, (((X j-(σ : ℂ)*A j)*(Y j-(σ : ℂ)*C j)+
      (Z j-(σ : ℂ)*D j)*(W j-(σ : ℂ)*F j))-(X j*Y j+Z j*W j))/den j‖ ≤
      (Fintype.card κ : ℝ)*(6*B^2*σ/δ) := by
    calc
      _ ≤ ∑ j, ‖(((X j-(σ : ℂ)*A j)*(Y j-(σ : ℂ)*C j)+
        (Z j-(σ : ℂ)*D j)*(W j-(σ : ℂ)*F j))-(X j*Y j+Z j*W j))/den j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : κ, 6*B^2*σ/δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_div]
        exact div_le_div₀ (by positivity)
          (pencil_pair_defect_le hσ0 hσ1 hB _ _ _ _ _ _ _ _
            (hX j) (hY j) (hZ j) (hW j) (hA j) (hC j) (hD j) (hF j)) hδ (hden j)
      _ = _ := by simp
  rw [heq]
  calc
    _ ≤ ‖-((σ : ℂ)*A2)-sv*aw-sw*av‖+
        ‖∑ j, (((X j-(σ : ℂ)*A j)*(Y j-(σ : ℂ)*C j)+
          (Z j-(σ : ℂ)*D j)*(W j-(σ : ℂ)*F j))-(X j*Y j+Z j*W j))/den j‖ := norm_add_le _ _
    _ ≤ ‖(σ : ℂ)*A2‖+‖sv*aw‖+‖sw*av‖+(Fintype.card κ : ℝ)*(6*B^2*σ/δ) := by
      apply add_le_add _ hs
      calc
        _ ≤ ‖-((σ : ℂ)*A2)-sv*aw‖+‖sw*av‖ := norm_sub_le _ _
        _ ≤ (‖-((σ : ℂ)*A2)‖+‖sv*aw‖)+‖sw*av‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ = _ := by rw [norm_neg]
    _ ≤ σ*B+Gv*B+Gw*B+(Fintype.card κ : ℝ)*(6*B^2*σ/δ) := by
      simp only [norm_mul,hn]
      gcongr
    _ = _ := by ring

end PowerConvexity
