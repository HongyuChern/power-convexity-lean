import PowerConvexity.Algebra.NormalizingFrameBoundsGeneral
import PowerConvexity.Algebra.MatrixEntryBoundsGeneral
import CHS.Calculus.ComplexFrame

/-! # Entry bounds for bounded constant complex frames in finite dimension -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixEntryBoundGeneral_transpose {A : Matrix ι ι ℂ} {B : ℝ}
    (hA : matrixEntryBoundGeneral A B) : matrixEntryBoundGeneral A.transpose B := by
  intro i j
  exact hA j i

theorem matrixEntryBoundGeneral_conjTranspose {A : Matrix ι ι ℂ} {B : ℝ}
    (hA : matrixEntryBoundGeneral A B) : matrixEntryBoundGeneral A.conjTranspose B := by
  intro i j
  simpa only [Matrix.conjTranspose_apply,norm_star] using hA j i

theorem matrixEntryBoundGeneral_weighted_sum {F : ι → Matrix ι ι ℂ}
    {c : ι → ℂ} {K T : ℝ} (hK : 0 ≤ K)
    (hc : ∀ r, ‖c r‖ ≤ K) (hF : ∀ r, matrixEntryBoundGeneral (F r) T) :
    matrixEntryBoundGeneral (∑ r,c r • F r) ((Fintype.card ι : ℝ)*K*T) := by
  intro i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ r, ‖c r * F r i j‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ι, K*T := Finset.sum_le_sum (fun r _ => by
      rw [norm_mul]; exact mul_le_mul (hc r) (hF r i j) (norm_nonneg _) hK)
    _ = _ := by simp; ring

theorem matrixEntryBoundGeneral_sandwich {P R F : Matrix ι ι ℂ} {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hP : matrixEntryBoundGeneral P K)
    (hR : matrixEntryBoundGeneral R K) (hF : matrixEntryBoundGeneral F T) :
    matrixEntryBoundGeneral (P*F*R) ((Fintype.card ι : ℝ)^2*K^2*T) := by
  convert matrixEntryBoundGeneral_mul (by positivity : 0 ≤ (Fintype.card ι : ℝ)*K*T)
    (matrixEntryBoundGeneral_mul hK hP hF) hR using 1 <;> ring

theorem matrix_mulVec_entry_bound_general {Q : Matrix ι ι ℂ}
    {v : ι → ℂ} {K T : ℝ} (hK : 0 ≤ K)
    (hQ : matrixEntryBoundGeneral Q K) (hv : ∀ j, ‖v j‖ ≤ T) (i : ι) :
    ‖Q.mulVec v i‖ ≤ (Fintype.card ι : ℝ)*K*T := by
  unfold Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ j, ‖Q i j*v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, K*T := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul]; exact mul_le_mul (hQ i j) (hv j) (norm_nonneg _) hK)
    _ = _ := by simp; ring

theorem complexFrame_norm_bound_general {Q : Matrix ι ι ℂ}
    (a b : ι → E) {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundGeneral Q K) (ha : ∀ j, ‖a j‖ ≤ T) (hb : ∀ j, ‖b j‖ ≤ T)
    (i : ι) :
    ‖complexFrameReal Q a b i‖ ≤ 2*(Fintype.card ι : ℝ)*K*T ∧
    ‖complexFrameImag Q a b i‖ ≤ 2*(Fintype.card ι : ℝ)*K*T := by
  have hre (j : ι) : ‖(Q i j).re‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hQ i j)
  have him (j : ι) : ‖(Q i j).im‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hQ i j)
  have hr (j : ι) : ‖(Q i j).re • a j+(Q i j).im • b j‖ ≤ 2*K*T := by
    calc
      _ ≤ ‖(Q i j).re • a j‖+‖(Q i j).im • b j‖ := norm_add_le _ _
      _ ≤ K*T+K*T := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul (hre j) (ha j) (norm_nonneg _) hK)
          (mul_le_mul (him j) (hb j) (norm_nonneg _) hK)
      _ = _ := by ring
  have hi (j : ι) : ‖(Q i j).re • b j-(Q i j).im • a j‖ ≤ 2*K*T := by
    calc
      _ ≤ ‖(Q i j).re • b j‖+‖(Q i j).im • a j‖ := norm_sub_le _ _
      _ ≤ K*T+K*T := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul (hre j) (hb j) (norm_nonneg _) hK)
          (mul_le_mul (him j) (ha j) (norm_nonneg _) hK)
      _ = _ := by ring
  constructor
  · unfold complexFrameReal
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hr j)).trans_eq (by simp; ring))
  · unfold complexFrameImag
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hi j)).trans_eq (by simp; ring))

end PowerConvexity
