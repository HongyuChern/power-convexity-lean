import CHS.Algebra.TraceDetConcavity

/-! # The actual supporting-plane error for varying positive determinants.
The equal-determinant condition is not inserted. When both densities are
at least one the trace error is bounded by their actual absolute difference.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem log_det_le_trace_sub_card_of_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Real.log A.det.re ≤ A.trace.re-(Fintype.card ι : ℝ) := by
  have hprod : (∏ i, hA.isHermitian.eigenvalues i) = A.det.re := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_prod,Complex.ofReal_re]
  have hlogs : (∑ i, Real.log (hA.isHermitian.eigenvalues i)) = Real.log A.det.re := by
    rw [← Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne'),hprod]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  rw [hlogs,Finset.sum_sub_distrib] at hsum
  rw [hA.isHermitian.trace_eq_sum_eigenvalues,Complex.re_sum]
  simpa only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hsum

theorem log_det_difference_le_inverse_trace {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det.re-Real.log A.det.re ≤ (A⁻¹*(B-A)).trace.re := by
  let S := CFC.sqrt A⁻¹
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A⁻¹).posSemidef
  have hSq : S*S = A⁻¹ := by
    simpa only [pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  have hAunit : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  have hSunit : IsUnit S.det := by
    have h := (isUnit_iff_isUnit_det _).mp hA.inv.isUnit
    rw [← hSq,det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  let C := S*B*S
  have hC : C.PosDef := by
    have h := hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).mpr hSunit))
    rw [hS.isHermitian.eq] at h
    exact h
  have hCdet : C.det = A⁻¹.det*B.det := by
    calc
      C.det = (S*S).det*B.det := by dsimp only [C]; simp only [det_mul]; ring
      _ = _ := by rw [hSq]
  have hAim : A.det.im = 0 := (Complex.pos_iff.mp hA.det_pos).2.symm
  have hBim : B.det.im = 0 := (Complex.pos_iff.mp hB.det_pos).2.symm
  have hinvim : A⁻¹.det.im = 0 := (Complex.pos_iff.mp hA.inv.det_pos).2.symm
  have hinvre : A⁻¹.det.re = (A.det.re)⁻¹ := by
    have hh := congrArg Complex.re (Matrix.det_nonsing_inv_mul_det A hAunit)
    simp only [Complex.mul_re,hAim,mul_zero,sub_zero,Complex.one_re] at hh
    apply (mul_right_cancel₀ (Complex.pos_iff.mp hA.det_pos).1.ne')
    rw [hh,inv_mul_cancel₀ (Complex.pos_iff.mp hA.det_pos).1.ne']
  have hCre : C.det.re = B.det.re/A.det.re := by
    rw [hCdet,Complex.mul_re,hBim,mul_zero,sub_zero,hinvre]
    ring
  have ht : C.trace = (A⁻¹*B).trace := by
    dsimp only [C]
    rw [trace_mul_cycle,hSq]
  have hh := log_det_le_trace_sub_card_of_posDef hC
  rw [hCre,Real.log_div (Complex.pos_iff.mp hB.det_pos).1.ne'
    (Complex.pos_iff.mp hA.det_pos).1.ne',ht] at hh
  rw [Matrix.mul_sub,Matrix.nonsing_inv_mul _ hAunit,Matrix.trace_sub,
    Complex.sub_re,Matrix.trace_one,Complex.natCast_re]
  exact hh

theorem abs_log_sub_le_abs_sub_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a-Real.log b| ≤ |a-b| := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb0 hab)),abs_of_nonneg (sub_nonneg.mpr hab)]
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have hq : a/b-1 = (a-b)/b := by field_simp
  rw [hq] at hl
  exact hl.trans (div_le_self (sub_nonneg.mpr hab) hb)

theorem inverse_trace_lower_of_density_difference {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (ha : 1 ≤ A.det.re) (hb : 1 ≤ B.det.re) :
    -|B.det.re-A.det.re| ≤ (A⁻¹*(B-A)).trace.re := by
  have hl := log_det_difference_le_inverse_trace hA hB
  have ha := abs_log_sub_le_abs_sub_of_one_le hb ha
  have hn := neg_le_abs (Real.log B.det.re-Real.log A.det.re)
  linarith

end PowerConvexity
