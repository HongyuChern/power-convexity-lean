import PowerConvexity.Algebra.DimensionTwo

/-! # Every entry is controlled by the real trace of a positive two-by-two matrix -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder
namespace PowerConvexity

theorem posSemidef_two_entry_trace_bounds {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (i j : Fin 2) :
    |(A i j).re| ≤ A.trace.re ∧ |(A i j).im| ≤ A.trace.re := by
  have h0 := Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))
  have h1 := Complex.nonneg_iff.mp (hA.diag_nonneg (i := 1))
  have h10 : A 1 0 = star (A 0 1) := (hA.isHermitian.apply 1 0).symm
  have hp := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ![1,1])).1
  have hm := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ![1,-1])).1
  have hi := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ![1,Complex.I])).1
  have hmi := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ![1,-Complex.I])).1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,h10,Complex.star_def,
    Complex.mul_re,Complex.mul_im] at hp hm hi hmi
  have htrace : A.trace.re = (A 0 0).re+(A 1 1).re := by
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have hr : |(A 0 1).re| ≤ A.trace.re := by rw [htrace,abs_le]; constructor <;> linarith [h0.1,h1.1]
  have him : |(A 0 1).im| ≤ A.trace.re := by rw [htrace,abs_le]; constructor <;> linarith [h0.1,h1.1]
  fin_cases i <;> fin_cases j
  · change |(A 0 0).re| ≤ A.trace.re ∧ |(A 0 0).im| ≤ A.trace.re
    rw [htrace,abs_of_nonneg h0.1,← h0.2,abs_zero]
    constructor <;> linarith [h0.1,h1.1]
  · exact ⟨hr,him⟩
  · change |(A 1 0).re| ≤ A.trace.re ∧ |(A 1 0).im| ≤ A.trace.re
    simpa only [h10,Complex.star_def,Complex.conj_re,Complex.conj_im,abs_neg] using And.intro hr him
  · change |(A 1 1).re| ≤ A.trace.re ∧ |(A 1 1).im| ≤ A.trace.re
    rw [htrace,abs_of_nonneg h1.1,← h1.2,abs_zero]
    constructor <;> linarith [h0.1,h1.1]

end PowerConvexity
