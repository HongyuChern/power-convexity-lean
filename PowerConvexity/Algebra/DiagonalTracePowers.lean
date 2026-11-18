import PowerConvexity.Calculus.TracePowers
import Mathlib.Algebra.Field.GeomSum

/-! # The diagonal trace and divided-power identities in B4-2 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_diagonal_power_mul (k : ι → ℂ) (X : Matrix ι ι ℂ) (n : ℕ) :
    (Matrix.diagonal k ^ n * X).trace = ∑ i, k i ^ n * X i i := by
  simp [Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

theorem trace_diagonal_mixed_powers (k : ι → ℂ) (X Y : Matrix ι ι ℂ) (j m : ℕ) :
    (Matrix.diagonal k ^ j * Y * Matrix.diagonal k ^ m * X).trace =
      ∑ l, ∑ t, k l ^ j * Y l t * k t ^ m * X t l := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow]
  change (∑ l, ∑ t,
    (Matrix.diagonal (k^j) * Y * Matrix.diagonal (k^m)) l t * X t l) = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.pow_apply]

theorem paper_B4_2_diagonal_trace_sum (k : ι → ℂ) (X Y : Matrix ι ι ℂ) (p : ℕ) :
    (∑ j ∈ Finset.range (p - 1),
      (Matrix.diagonal k ^ j * Y * Matrix.diagonal k ^ (p - 2 - j) * X).trace) =
      ∑ j ∈ Finset.range (p - 1), ∑ l, ∑ m,
        k l ^ j * Y l m * k m ^ (p - 2 - j) * X m l := by
  simp_rw [trace_diagonal_mixed_powers]

theorem divided_power_sum_distinct (a b : ℂ) (hab : a ≠ b) (n : ℕ) :
    (∑ j ∈ Finset.range n, a^j * b^(n - 1 - j)) = (a^n - b^n) / (a-b) :=
  geom₂_sum hab n

theorem divided_power_sum_equal (a : ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), a^j * a^(n-j)) = (n + 1 : ℕ) * a^n := by
  have he (j : ℕ) (hj : j ∈ Finset.range (n + 1)) : a^j * a^(n-j) = a^n := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [Finset.sum_congr rfl he]
  simp [nsmul_eq_mul]

end PowerConvexity
