import PowerConvexity.Algebra.NormalizingFrameBoundsTwo
import CHS.Calculus.ComplexFrame

/-! # Entry bounds for arbitrary bounded constant complex frames -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixEntryBoundTwo_transpose {A : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ}
    (hA : matrixEntryBoundTwo A B) : matrixEntryBoundTwo A.transpose B := by
  intro i j
  exact hA j i

theorem matrixEntryBoundTwo_conjTranspose {A : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ}
    (hA : matrixEntryBoundTwo A B) : matrixEntryBoundTwo A.conjTranspose B := by
  intro i j
  simpa only [Matrix.conjTranspose_apply,norm_star] using hA j i

theorem matrixEntryBoundTwo_weighted_sum {F : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    {c : Fin 2 → ℂ} {K T : ℝ} (hK : 0 ≤ K)
    (hc : ∀ r, ‖c r‖ ≤ K) (hF : ∀ r, matrixEntryBoundTwo (F r) T) :
    matrixEntryBoundTwo (∑ r,c r • F r) (2*K*T) := by
  rw [Fin.sum_univ_two]
  convert matrixEntryBoundTwo_add (matrixEntryBoundTwo_smul hK (hc 0) (hF 0))
    (matrixEntryBoundTwo_smul hK (hc 1) (hF 1)) using 1 <;> ring

theorem matrixEntryBoundTwo_sandwich {P R F : Matrix (Fin 2) (Fin 2) ℂ} {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hP : matrixEntryBoundTwo P K)
    (hR : matrixEntryBoundTwo R K) (hF : matrixEntryBoundTwo F T) :
    matrixEntryBoundTwo (P*F*R) (4*K^2*T) := by
  convert matrixEntryBoundTwo_mul (by positivity : 0 ≤ 2*K*T)
    (matrixEntryBoundTwo_mul hK hP hF) hR using 1 <;> ring

theorem matrix_mulVec_entry_bound_two {Q : Matrix (Fin 2) (Fin 2) ℂ}
    {v : Fin 2 → ℂ} {K T : ℝ} (hK : 0 ≤ K)
    (hQ : matrixEntryBoundTwo Q K) (hv : ∀ j, ‖v j‖ ≤ T) (i : Fin 2) :
    ‖Q.mulVec v i‖ ≤ 2*K*T := by
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  calc
    _ ≤ ‖Q i 0*v 0‖+‖Q i 1*v 1‖ := norm_add_le _ _
    _ ≤ K*T+K*T := by simp only [norm_mul]; gcongr <;> first | exact hQ _ _ | exact hv _
    _ = _ := by ring

theorem complexFrame_norm_bound_two {Q : Matrix (Fin 2) (Fin 2) ℂ}
    (a b : Fin 2 → E) {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundTwo Q K) (ha : ∀ j, ‖a j‖ ≤ T) (hb : ∀ j, ‖b j‖ ≤ T)
    (i : Fin 2) :
    ‖complexFrameReal Q a b i‖ ≤ 4*K*T ∧ ‖complexFrameImag Q a b i‖ ≤ 4*K*T := by
  have hre (j : Fin 2) : ‖(Q i j).re‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hQ i j)
  have him (j : Fin 2) : ‖(Q i j).im‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hQ i j)
  have hr (j : Fin 2) : ‖(Q i j).re • a j+(Q i j).im • b j‖ ≤ 2*K*T := by
    calc
      _ ≤ ‖(Q i j).re • a j‖+‖(Q i j).im • b j‖ := norm_add_le _ _
      _ ≤ K*T+K*T := by simp only [norm_smul]; gcongr <;> first | exact hre _ | exact him _ | exact ha _ | exact hb _
      _ = _ := by ring
  have hi (j : Fin 2) : ‖(Q i j).re • b j-(Q i j).im • a j‖ ≤ 2*K*T := by
    calc
      _ ≤ ‖(Q i j).re • b j‖+‖(Q i j).im • a j‖ := norm_sub_le _ _
      _ ≤ K*T+K*T := by simp only [norm_smul]; gcongr <;> first | exact hre _ | exact him _ | exact ha _ | exact hb _
      _ = _ := by ring
  constructor
  · unfold complexFrameReal
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hr j)).trans (by simp [Fin.sum_univ_two]; ring_nf; rfl))
  · unfold complexFrameImag
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hi j)).trans (by simp [Fin.sum_univ_two]; ring_nf; rfl))

end PowerConvexity
