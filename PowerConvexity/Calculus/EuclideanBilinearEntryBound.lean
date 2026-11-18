import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Operator norm from entries in the Euclidean orthonormal basis

These estimates convert the entrywise CHS Hessian modulus into the actual
operator norm of the iterated Fréchet derivative. No differentiability or
symmetry is needed for this finite-dimensional step.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace PowerConvexity

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem euclidean_linearMap_norm_le_of_basis_bound
    (L : EuclideanSpace ℝ ι →L[ℝ] F) {M : ℝ} (hM : 0 ≤ M)
    (hL : ∀ i, ‖L (EuclideanSpace.single i 1)‖ ≤ M) :
    ‖L‖ ≤ (Fintype.card ι : ℝ) * M := by
  apply L.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hM)
  intro x
  have hx : (∑ i, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using (EuclideanSpace.basisFun ι ℝ).sum_repr x
  calc
    ‖L x‖ = ‖∑ i, x i • L (EuclideanSpace.single i 1)‖ := by
      conv_lhs => rw [← hx]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖x i • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖x‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le x i) (hL i) (norm_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι : ℝ) * M * ‖x‖ := by simp; ring

theorem euclidean_bilinear_norm_le_of_entry_bound
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hH : ∀ i j, |H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M) :
    ‖H‖ ≤ (Fintype.card ι : ℝ)^2 * M := by
  have hrow (i : ι) : ‖H (EuclideanSpace.single i 1)‖ ≤ (Fintype.card ι : ℝ) * M :=
    euclidean_linearMap_norm_le_of_basis_bound _ hM (fun j => by
      simpa only [Real.norm_eq_abs] using hH i j)
  have hh := euclidean_linearMap_norm_le_of_basis_bound H
    (mul_nonneg (Nat.cast_nonneg _) hM) hrow
  convert hh using 1 <;> ring

end PowerConvexity
