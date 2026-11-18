import PowerConvexity.Algebra.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.ClosureVariableDensity

/-! # The actual determinant transfers mixed moduli to the pure normal entry

The denominator is the positive tangential complex diagonal at one actual
point. The other normal diagonal is only required to have the already known
C2 bound. This is a difference estimate, not just a bound for each matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Matrix
open scoped ComplexOrder
namespace PowerConvexity

theorem actual_complex_normSq_difference_bound_two (z w : ℂ) :
    |Complex.normSq z-Complex.normSq w| ≤ (‖z‖+‖w‖)*‖z-w‖ := by
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,
    show ‖z‖^2-‖w‖^2=(‖z‖-‖w‖)*(‖z‖+‖w‖) by ring,
    abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

theorem actual_positive_hermitian_diagonal_determinant_identity_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) :
    (A 0 0).re*(A 1 1).re=A.det.re+Complex.normSq (A 0 1) := by
  have h00 := Complex.pos_iff.mp (hA.diag_pos (i := 0))
  have h11 := Complex.pos_iff.mp (hA.diag_pos (i := 1))
  have h10 : A 1 0=star (A 0 1) := (hA.isHermitian.apply 1 0).symm
  rw [Matrix.det_fin_two,h10]
  simp only [Complex.sub_re,Complex.mul_re,← h00.2,← h11.2,Complex.star_def,
    Complex.conj_re,Complex.conj_im,zero_mul,sub_zero,Complex.normSq_apply]
  ring

theorem actual_positive_hermitian_normal_difference_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {delta : ℝ} (hd : 0 < delta) (h00 : delta ≤ (A 0 0).re) :
    |(A 1 1).re-(B 1 1).re| ≤
      (|A.det.re-B.det.re|+(‖A 0 1‖+‖B 0 1‖)*‖A 0 1-B 0 1‖+
        |(B 1 1).re| * |(A 0 0).re-(B 0 0).re|)/delta := by
  have hidA := actual_positive_hermitian_diagonal_determinant_identity_two hA
  have hidB := actual_positive_hermitian_diagonal_determinant_identity_two hB
  have hid : (A 0 0).re*((A 1 1).re-(B 1 1).re)=
      (A.det.re-B.det.re)+(Complex.normSq (A 0 1)-Complex.normSq (B 0 1))-
        (B 1 1).re*((A 0 0).re-(B 0 0).re) := by nlinarith only [hidA,hidB]
  have ha0 : 0 ≤ (A 0 0).re := hd.le.trans h00
  apply (le_div_iff₀ hd).mpr
  calc
    |(A 1 1).re-(B 1 1).re| * delta ≤ |(A 1 1).re-(B 1 1).re| * (A 0 0).re :=
      mul_le_mul_of_nonneg_left h00 (abs_nonneg _)
    _ = |(A 0 0).re*((A 1 1).re-(B 1 1).re)| := by rw [abs_mul,abs_of_nonneg ha0]; ring
    _ = |(A.det.re-B.det.re)+(Complex.normSq (A 0 1)-Complex.normSq (B 0 1))-
        (B 1 1).re*((A 0 0).re-(B 0 0).re)| := congrArg abs hid
    _ ≤ (|A.det.re-B.det.re|+|Complex.normSq (A 0 1)-Complex.normSq (B 0 1)|)+
        |(B 1 1).re*((A 0 0).re-(B 0 0).re)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (add_le_add le_rfl (actual_complex_normSq_difference_bound_two _ _)) le_rfl

theorem actual_positive_hermitian_normal_modulus_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {delta K M ed em et : ℝ} (hd : 0 < delta) (h00 : delta ≤ (A 0 0).re)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hdet : |A.det.re-B.det.re| ≤ ed)
    (hAz : ‖A 0 1‖ ≤ K) (hBz : ‖B 0 1‖ ≤ K)
    (hmixed : ‖A 0 1-B 0 1‖ ≤ em)
    (hnorm : |(B 1 1).re| ≤ M) (htan : |(A 0 0).re-(B 0 0).re| ≤ et) :
    |(A 1 1).re-(B 1 1).re| ≤ (ed+2*K*em+M*et)/delta := by
  apply (actual_positive_hermitian_normal_difference_two hA hB hd h00).trans
  apply div_le_div_of_nonneg_right _ hd.le
  have hz : ‖A 0 1‖+‖B 0 1‖ ≤ 2*K := by linarith
  exact add_le_add
    (add_le_add hdet (mul_le_mul hz hmixed (norm_nonneg _) (by positivity)))
    (mul_le_mul hnorm htan (abs_nonneg _) hM)

end PowerConvexity
