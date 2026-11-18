import PowerConvexity.Algebra.FullQuadraticCompletionTwo
import PowerConvexity.Algebra.MatrixEntryBoundsTwo
import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # Bounds for the two off-diagonal spectral vectors and their remainders -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PowerConvexity

theorem contactShiftedColumn_entry_bound_two {B : ℝ} (hB : 0 ≤ B)
    (W : Matrix (Fin 2) (Fin 2) ℂ) (τ : ℂ)
    (hW : matrixEntryBoundTwo W B) (hτ : ‖τ‖ ≤ B) (p s : Fin 2) :
    ‖W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s‖ ≤ 2*B := by
  calc
    _ ≤ ‖W p s‖+‖τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s‖ := norm_add_le _ _
    _ ≤ B+B*1 := by
      rw [norm_mul]
      gcongr
      · exact hW p s
      · exact matrixEntryBoundTwo_one p s
    _ = _ := by ring

theorem contactVector_norm_bounds_two {B b : ℝ} (hB : 0 ≤ B)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (W D : Matrix (Fin 2) (Fin 2) ℂ) (τ : ℂ)
    (hW : matrixEntryBoundTwo W B) (hD : matrixEntryBoundTwo D B) (hτ : ‖τ‖ ≤ B)
    (p : Fin 2) :
    ‖contactUpperVectorTwo W D τ b p‖ ≤ 3*B ∧
    ‖contactLowerVectorTwo W D τ b p‖ ≤ 3*B := by
  have hbn : ‖(b:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,abs_of_nonneg hb0] using hb1
  have hX := contactShiftedColumn_entry_bound_two hB W τ hW hτ p 1
  constructor
  · unfold contactUpperVectorTwo
    calc
      _ ≤ ‖W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1‖+‖(b:ℂ)*D p 1‖ := norm_sub_le _ _
      _ ≤ 2*B+1*B := by
        rw [norm_mul]
        gcongr
        exact hD p 1
      _ = _ := by ring
  · unfold contactLowerVectorTwo
    calc
      _ ≤ ‖(b:ℂ)*(W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1)‖+‖D p 1‖ := norm_sub_le _ _
      _ ≤ 1*(2*B)+B := by rw [norm_mul]; gcongr; exact hD p 1
      _ = _ := by ring

theorem schurLowerRemainder_norm_bound {B t b : ℝ} (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (H R A C : ℂ) (hH : ‖H‖ ≤ 3*B) (hR : ‖R‖ ≤ B) (hA : ‖A‖ ≤ B) (hC : ‖C‖ ≤ B) :
    ‖-H+(b:ℂ)*(t:ℂ)*R+(1+(t:ℂ))*(A-(b:ℂ)*C)‖ ≤ 8*B := by
  have hbn : ‖(b:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,abs_of_nonneg hb0] using hb1
  have htn : ‖(t:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,abs_of_nonneg ht0] using ht1
  have hsn : ‖1+(t:ℂ)‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hAC : ‖A-(b:ℂ)*C‖ ≤ 2*B := by
    calc
      _ ≤ ‖A‖+‖(b:ℂ)*C‖ := norm_sub_le _ _
      _ ≤ B+1*B := by rw [norm_mul]; gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖-H+(b:ℂ)*(t:ℂ)*R‖+‖(1+(t:ℂ))*(A-(b:ℂ)*C)‖ := norm_add_le _ _
    _ ≤ (‖H‖+‖(b:ℂ)*(t:ℂ)*R‖)+‖(1+(t:ℂ))*(A-(b:ℂ)*C)‖ := by
      exact add_le_add (by simpa using norm_add_le (-H) ((b:ℂ)*(t:ℂ)*R)) le_rfl
    _ ≤ (3*B+1*1*B)+2*(2*B) := by simp only [norm_mul]; gcongr
    _ = _ := by ring

theorem schurVector_sigma_error_bound {B K t σ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hσ : σ = 1-t^2) (V U R A : ℂ) (hR : ‖R‖ ≤ K*B) (hA : ‖A‖ ≤ B)
    (hV : V = U+(1-(t:ℂ))*R-(σ:ℂ)*A) :
    ‖V-U‖ ≤ (K+1)*B*σ := by
  obtain ⟨hδ,hδσ,hσ0⟩ := one_sub_takagi_le_sigma ht0 ht1 hσ
  have htn : ‖1-(t:ℂ)‖ = 1-t := by
    rw [show 1-(t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; rfl]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
  have hσn : ‖(σ:ℂ)‖ = σ := by simp [Complex.norm_real,abs_of_nonneg hσ0]
  have he : V-U = (1-(t:ℂ))*R-(σ:ℂ)*A := by rw [hV]; ring
  rw [he]
  calc
    _ ≤ ‖(1-(t:ℂ))*R‖+‖(σ:ℂ)*A‖ := norm_sub_le _ _
    _ = (1-t)*‖R‖+σ*‖A‖ := by rw [norm_mul,norm_mul,htn,hσn]
    _ ≤ σ*(K*B)+σ*B := by gcongr
    _ = _ := by ring

theorem vector_norm_le_of_sigma_error {B K σ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (V U : ℂ) (hU : ‖U‖ ≤ 3*B) (hD : ‖V-U‖ ≤ K*B*σ) :
    ‖V‖ ≤ (3+K)*B := by
  calc
    _ ≤ ‖V-U‖+‖U‖ := by simpa using norm_add_le (V-U) U
    _ ≤ K*B*σ+3*B := add_le_add hD hU
    _ ≤ K*B*1+3*B := by gcongr
    _ = _ := by ring

end PowerConvexity
