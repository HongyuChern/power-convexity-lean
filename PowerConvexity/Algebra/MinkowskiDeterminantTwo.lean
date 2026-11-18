import PowerConvexity.Algebra.DeterminantOrderTwo

/-! # Two-dimensional determinant concavity for a supplementary direct route

This algebra is independent of the frozen spectral minimum proof. Its role is
recorded as supplementary; it is not itself a power-convexity endpoint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder
namespace PowerConvexity

theorem hermitian_trace_discriminant_nonneg_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) :
    4*A.det.re ≤ A.trace.re^2 := by
  have h00 := congrArg Complex.im (hA.apply 0 0)
  have h11 := congrArg Complex.im (hA.apply 1 1)
  simp only [Complex.star_def,Complex.conj_im] at h00 h11
  have hi0 : (A 0 0).im = 0 := by linarith
  have hi1 : (A 1 1).im = 0 := by linarith
  have h10 : A 1 0 = star (A 0 1) := (hA.apply 1 0).symm
  rw [Matrix.det_fin_two,h10]
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Complex.add_re,Complex.sub_re,
    Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,hi0,hi1]
  nlinarith [sq_nonneg ((A 0 0).re-(A 1 1).re),sq_nonneg (A 0 1).re,sq_nonneg (A 0 1).im]

theorem two_sqrt_det_re_le_trace {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    2*Real.sqrt A.det.re ≤ A.trace.re := by
  have ht : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hd : 0 ≤ A.det.re := (Complex.nonneg_iff.mp hA.det_nonneg).1
  have hh := hermitian_trace_discriminant_nonneg_two hA.isHermitian
  nlinarith [Real.sq_sqrt hd,Real.sqrt_nonneg A.det.re]

theorem sqrt_det_re_add_superadditive_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hB : B.PosSemidef) :
    Real.sqrt A.det.re+Real.sqrt B.det.re ≤ Real.sqrt (A+B).det.re := by
  obtain ⟨Q,hQ,hQA⟩ := exists_complex_normalization hA
  let C := Q*B*Q.conjTranspose
  let q := Complex.normSq Q.det
  have hC : C.PosSemidef := hB.mul_mul_conjTranspose_same Q
  have ha : 0 < A.det.re := (Complex.pos_iff.mp hA.det_pos).1
  have hb : 0 ≤ B.det.re := (Complex.nonneg_iff.mp hB.det_nonneg).1
  have hc : 0 ≤ C.det.re := (Complex.nonneg_iff.mp hC.det_nonneg).1
  have hsum : 0 ≤ (A+B).det.re := (Complex.nonneg_iff.mp
    (hA.add_posSemidef hB).posSemidef.det_nonneg).1
  have hqa : q*A.det.re = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det.re) hQA
    rw [determinant_complex_congruence] at hh
    simpa only [q,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Matrix.det_one,Complex.one_re] using hh
  have hcb : C.det.re = q*B.det.re := by
    dsimp only [C]
    rw [determinant_complex_congruence]
    simp only [q,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hac : A.det.re*C.det.re = B.det.re := by
    rw [hcb]
    calc
      A.det.re*(q*B.det.re) = (q*A.det.re)*B.det.re := by ring
      _ = B.det.re := by rw [hqa,one_mul]
  have hQS : Q*(A+B)*Q.conjTranspose = C+1 := by
    rw [Matrix.mul_add,Matrix.add_mul,hQA]
    dsimp [C]
    abel
  have hqs : q*(A+B).det.re = 1+C.trace.re+C.det.re := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det.re) hQS
    rw [determinant_complex_congruence] at hh
    have he : (C+1).det = C.det+C.trace+1 := by
      simpa only [one_smul,one_mul,one_pow] using det_add_scalar_one_two C 1
    rw [he] at hh
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.add_re,Complex.one_re] at hh
    dsimp only [q]
    linarith
  have hS : (A+B).det.re = A.det.re*(1+C.trace.re+C.det.re) := by
    calc
      (A+B).det.re = (q*A.det.re)*(A+B).det.re := by rw [hqa,one_mul]
      _ = A.det.re*(q*(A+B).det.re) := by ring
      _ = _ := by rw [hqs]
  have hsqr : Real.sqrt B.det.re = Real.sqrt A.det.re*Real.sqrt C.det.re := by
    rw [← hac,Real.sqrt_mul ha.le]
  have hroot : Real.sqrt A.det.re*Real.sqrt B.det.re = A.det.re*Real.sqrt C.det.re := by
    rw [hsqr]
    calc
      Real.sqrt A.det.re*(Real.sqrt A.det.re*Real.sqrt C.det.re) =
        (Real.sqrt A.det.re)^2*Real.sqrt C.det.re := by ring
      _ = _ := by rw [Real.sq_sqrt ha.le]
  have htrace := mul_le_mul_of_nonneg_left (two_sqrt_det_re_le_trace hC) ha.le
  have hbound : (Real.sqrt A.det.re+Real.sqrt B.det.re)^2 ≤ (A+B).det.re := by
    rw [add_sq,Real.sq_sqrt ha.le,Real.sq_sqrt hb,hS]
    have hr : 2*Real.sqrt A.det.re*Real.sqrt B.det.re = 2*A.det.re*Real.sqrt C.det.re := by
      nlinarith [hroot]
    rw [hr]
    nlinarith [hac]
  nlinarith [Real.sq_sqrt hsum,Real.sqrt_nonneg (A+B).det.re,
    Real.sqrt_nonneg A.det.re,Real.sqrt_nonneg B.det.re]

end PowerConvexity
