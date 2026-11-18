import PowerConvexityComparator.DimensionRemarkProblem
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators Matrix
namespace PowerConvexityComparator.DimensionRemarkSolution
open DimensionRemarkProblem

theorem scalarIdentityAnswer : ScalarIdentityStatement := by
  intro m C
  have h : C^2+1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem counterexampleAnswer : CounterexampleStatement := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    have hk : 2 ≤ k := by omega
    have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
    let d : Fin (k+1) → ℂ := Fin.cases (((-(k:ℝ)/5:ℝ):ℂ)*Complex.I) (fun _ => Complex.I)
    let r : Fin (k+1) → ℂ := Fin.cases 2 (fun _ => 0)
    refine ⟨Matrix.diagonal d,r,?_,?_,?_⟩
    · rw [Matrix.diagonal_conjTranspose]
      ext i j
      by_cases hij : i=j
      · subst j
        simp only [Matrix.diagonal_apply_eq,Matrix.neg_apply]
        refine Fin.cases ?_ (fun l => ?_) i <;> simp [d]
      · simp [Matrix.diagonal_apply,hij]
    · have he : (∑ p,∑ q,((1 : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) q p+
          r q*star (r p))*Matrix.diagonal d p q) =
          ∑ p,(1+r p*star (r p))*d p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [Matrix.diagonal_apply,mul_ite]
      rw [he,Fin.sum_univ_succ]
      simp [r,d]
      push_cast
      ring
    · have hnorm : (∑ p,∑ q,Complex.normSq (Matrix.diagonal d p q)) =
          (k:ℝ)+(k:ℝ)^2/25 := by
        have he : (∑ p,∑ q,Complex.normSq (Matrix.diagonal d p q)) =
            ∑ p,Complex.normSq (d p) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [Matrix.diagonal_apply,apply_ite]
        rw [he,Fin.sum_univ_succ]
        simp [d,Complex.normSq_mul]
        ring
      have htrace : (Matrix.diagonal d).trace = (((4*(k:ℝ)/5:ℝ):ℂ)*Complex.I) := by
        rw [Matrix.trace_diagonal,Fin.sum_univ_succ]
        simp [d]
        push_cast
        ring
      rw [hnorm,htrace]
      simp only [Complex.normSq_mul,Complex.normSq_ofReal,Complex.normSq_I,mul_one]
      have hp : 0 ≤ ((k:ℝ)-2)*(k:ℝ) := mul_nonneg (by linarith) (by positivity)
      nlinarith

end PowerConvexityComparator.DimensionRemarkSolution
