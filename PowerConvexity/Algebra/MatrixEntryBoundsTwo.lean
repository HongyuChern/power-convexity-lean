import PowerConvexity.Algebra.ResidualCombination

/-! # Explicit entry bounds for the finite two-dimensional contraction algebra -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
open CHS.SchurContractionCore

def matrixEntryBoundTwo (A : Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ) : Prop :=
  ∀ i j, ‖A i j‖ ≤ B

theorem matrixEntryBoundTwo_mono {A : Matrix (Fin 2) (Fin 2) ℂ} {B C : ℝ}
    (hA : matrixEntryBoundTwo A B) (hBC : B ≤ C) : matrixEntryBoundTwo A C :=
  fun i j => (hA i j).trans hBC

theorem matrixEntryBoundTwo_zero {B : ℝ} (hB : 0 ≤ B) :
    matrixEntryBoundTwo (0 : Matrix (Fin 2) (Fin 2) ℂ) B := by
  intro i j
  simpa using hB

theorem matrixEntryBoundTwo_one :
    matrixEntryBoundTwo (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  intro i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.one_apply,hij]

theorem matrixEntryBoundTwo_add {A B : Matrix (Fin 2) (Fin 2) ℂ} {M N : ℝ}
    (hA : matrixEntryBoundTwo A M) (hB : matrixEntryBoundTwo B N) :
    matrixEntryBoundTwo (A+B) (M+N) := by
  intro i j
  exact (norm_add_le (A i j) (B i j)).trans (add_le_add (hA i j) (hB i j))

theorem matrixEntryBoundTwo_sub {A B : Matrix (Fin 2) (Fin 2) ℂ} {M N : ℝ}
    (hA : matrixEntryBoundTwo A M) (hB : matrixEntryBoundTwo B N) :
    matrixEntryBoundTwo (A-B) (M+N) := by
  intro i j
  exact (norm_sub_le (A i j) (B i j)).trans (add_le_add (hA i j) (hB i j))

theorem matrixEntryBoundTwo_map_star {A : Matrix (Fin 2) (Fin 2) ℂ} {M : ℝ}
    (hA : matrixEntryBoundTwo A M) : matrixEntryBoundTwo (A.map star) M := by
  intro i j
  simpa only [Matrix.map_apply,norm_star] using hA i j

theorem matrixEntryBoundTwo_mul {A B : Matrix (Fin 2) (Fin 2) ℂ} {M N : ℝ}
    (hM : 0 ≤ M) (hA : matrixEntryBoundTwo A M) (hB : matrixEntryBoundTwo B N) :
    matrixEntryBoundTwo (A*B) (2*M*N) := by
  intro i j
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  calc
    _ ≤ ‖A i 0*B 0 j‖+‖A i 1*B 1 j‖ := norm_add_le _ _
    _ = ‖A i 0‖*‖B 0 j‖+‖A i 1‖*‖B 1 j‖ := by rw [norm_mul,norm_mul]
    _ ≤ M*N+M*N := add_le_add
      (mul_le_mul (hA i 0) (hB 0 j) (norm_nonneg _) hM)
      (mul_le_mul (hA i 1) (hB 1 j) (norm_nonneg _) hM)
    _ = _ := by ring

theorem matrixEntryBoundTwo_smul {A : Matrix (Fin 2) (Fin 2) ℂ} {M N : ℝ}
    (hM : 0 ≤ M) {c : ℂ} (hc : ‖c‖ ≤ M) (hA : matrixEntryBoundTwo A N) :
    matrixEntryBoundTwo (c • A) (M*N) := by
  intro i j
  change ‖c*A i j‖ ≤ M*N
  rw [norm_mul]
  exact mul_le_mul hc (hA i j) (norm_nonneg _) hM

theorem matrixEntryBoundTwo_contract {G : Matrix (Fin 2) (Fin 2) ℂ}
    {F : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ} {M N : ℝ}
    (hM : 0 ≤ M) (hG : matrixEntryBoundTwo G M)
    (hF : ∀ p q, matrixEntryBoundTwo (F p q) N) :
    matrixEntryBoundTwo (contract G F) (4*M*N) := by
  intro i j
  simp only [contract,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ p,‖∑ q,G q p*F p q i j‖ := norm_sum_le _ _
    _ ≤ ∑ p,∑ q,‖G q p*F p q i j‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_sum_le _ _
    _ ≤ ∑ _p : Fin 2,∑ _q : Fin 2,M*N := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      exact mul_le_mul (hG q p) (hF p q i j) (norm_nonneg _) hM
    _ = _ := by simp [Fin.sum_univ_two]; ring

end PowerConvexity
