import PowerConvexity.Algebra.ResidualCombination

/-! # Explicit entry bounds for the arbitrary finite-dimensional contraction algebra -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open CHS.SchurContractionCore

def matrixEntryBoundGeneral (A : Matrix ι ι ℂ) (B : ℝ) : Prop :=
  ∀ i j, ‖A i j‖ ≤ B

theorem matrixEntryBoundGeneral_mono {A : Matrix ι ι ℂ} {B C : ℝ}
    (hA : matrixEntryBoundGeneral A B) (hBC : B ≤ C) : matrixEntryBoundGeneral A C :=
  fun i j => (hA i j).trans hBC

theorem matrixEntryBoundGeneral_zero {B : ℝ} (hB : 0 ≤ B) :
    matrixEntryBoundGeneral (0 : Matrix ι ι ℂ) B := by
  intro i j
  simpa using hB

theorem matrixEntryBoundGeneral_one :
    matrixEntryBoundGeneral (1 : Matrix ι ι ℂ) 1 := by
  intro i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.one_apply,hij]

theorem matrixEntryBoundGeneral_add {A B : Matrix ι ι ℂ} {M N : ℝ}
    (hA : matrixEntryBoundGeneral A M) (hB : matrixEntryBoundGeneral B N) :
    matrixEntryBoundGeneral (A+B) (M+N) := by
  intro i j
  exact (norm_add_le (A i j) (B i j)).trans (add_le_add (hA i j) (hB i j))

theorem matrixEntryBoundGeneral_sub {A B : Matrix ι ι ℂ} {M N : ℝ}
    (hA : matrixEntryBoundGeneral A M) (hB : matrixEntryBoundGeneral B N) :
    matrixEntryBoundGeneral (A-B) (M+N) := by
  intro i j
  exact (norm_sub_le (A i j) (B i j)).trans (add_le_add (hA i j) (hB i j))

theorem matrixEntryBoundGeneral_map_star {A : Matrix ι ι ℂ} {M : ℝ}
    (hA : matrixEntryBoundGeneral A M) : matrixEntryBoundGeneral (A.map star) M := by
  intro i j
  simpa only [Matrix.map_apply,norm_star] using hA i j

theorem matrixEntryBoundGeneral_mul {A B : Matrix ι ι ℂ} {M N : ℝ}
    (hM : 0 ≤ M) (hA : matrixEntryBoundGeneral A M) (hB : matrixEntryBoundGeneral B N) :
    matrixEntryBoundGeneral (A*B) ((Fintype.card ι : ℝ)*M*N) := by
  intro i j
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖A i k*B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : ι, M*N := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hM
    _ = _ := by simp; ring

theorem matrixEntryBoundGeneral_smul {A : Matrix ι ι ℂ} {M N : ℝ}
    (hM : 0 ≤ M) {c : ℂ} (hc : ‖c‖ ≤ M) (hA : matrixEntryBoundGeneral A N) :
    matrixEntryBoundGeneral (c • A) (M*N) := by
  intro i j
  change ‖c*A i j‖ ≤ M*N
  rw [norm_mul]
  exact mul_le_mul hc (hA i j) (norm_nonneg _) hM

theorem matrixEntryBoundGeneral_contract {G : Matrix ι ι ℂ}
    {F : ι → ι → Matrix ι ι ℂ} {M N : ℝ}
    (hM : 0 ≤ M) (hG : matrixEntryBoundGeneral G M)
    (hF : ∀ p q, matrixEntryBoundGeneral (F p q) N) :
    matrixEntryBoundGeneral (contract G F) ((Fintype.card ι : ℝ)^2*M*N) := by
  intro i j
  simp only [contract,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ p,‖∑ q,G q p*F p q i j‖ := norm_sum_le _ _
    _ ≤ ∑ p,∑ q,‖G q p*F p q i j‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_sum_le _ _
    _ ≤ ∑ _p : ι,∑ _q : ι,M*N := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      exact mul_le_mul (hG q p) (hF p q i j) (norm_nonneg _) hM
    _ = _ := by simp; ring

end PowerConvexity
