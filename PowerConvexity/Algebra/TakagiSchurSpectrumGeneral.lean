import PowerConvexity.Algebra.TakagiGeneral
import PowerConvexity.Algebra.TakagiSchurSpectrumTwo
import PowerConvexity.Calculus.ModifiedEigenvalueGeneral

/-! # General Takagi normalization and the actual minimum Schur eigenvalue -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_simultaneous_takagi {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit Q.det ∧ Q*A*Q.conjTranspose = 1 ∧
      (∀ i, 0 ≤ d i) ∧ Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)) := by
  obtain ⟨P,hP,hPA⟩ := exists_complex_normalization hA
  have hBP : (P*B*P.transpose).transpose = P*B*P.transpose := by
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hB]
    noncomm_ring
  obtain ⟨U,d,hU,hUU,hd,hdiag⟩ := exists_takagi hBP
  refine ⟨U*P,d,?_,?_,hd,?_⟩
  · rw [Matrix.det_mul]; exact hU.mul hP
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = U*(P*A*P.conjTranspose)*U.conjTranspose := by noncomm_ring
      _ = 1 := by rw [hPA,Matrix.mul_one,hUU]
  · rw [Matrix.transpose_mul]
    calc
      _ = U*(P*B*P.transpose)*U.transpose := by noncomm_ring
      _ = _ := hdiag

theorem hasEigenvalue_of_charpoly_eq {K L : Matrix ι ι ℂ}
    (h : K.charpoly = L.charpoly) (z : ℂ) :
    Module.End.HasEigenvalue K.toLin' z ↔ Module.End.HasEigenvalue L.toLin' z := by
  simp only [Module.End.hasEigenvalue_iff_isRoot_charpoly,Matrix.charpoly_toLin',h]

theorem smallestRealEigenvalue_of_charpoly_eq {K L : Matrix ι ι ℂ}
    (h : K.charpoly = L.charpoly) : smallestRealEigenvalue K = smallestRealEigenvalue L := by
  unfold smallestRealEigenvalue
  congr 1
  ext t
  exact hasEigenvalue_of_charpoly_eq h (t:ℂ)

theorem real_diagonal_hasEigenvalue_iff (d : ι → ℝ) (t : ℝ) :
    Module.End.HasEigenvalue (Matrix.diagonal (fun i => (d i:ℂ))).toLin' (t:ℂ) ↔
      ∃ i, d i = t := by
  rw [matrix_hasEigenvalue_iff_det_sub_eq_zero]
  have h : (Matrix.diagonal (fun i => (d i:ℂ))-(t:ℂ) • 1) =
      Matrix.diagonal (fun i => ((d i-t:ℝ):ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  rw [h,Matrix.det_diagonal]
  simp only [Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,Complex.ofReal_eq_zero,sub_eq_zero]

theorem smallestRealEigenvalue_diagonal (d : ι → ℝ) (i : ι)
    (hmin : ∀ j, d i ≤ d j) :
    smallestRealEigenvalue (Matrix.diagonal (fun j => (d j:ℂ))) = d i := by
  apply IsLeast.csInf_eq
  constructor
  · exact (real_diagonal_hasEigenvalue_iff d (d i)).mpr ⟨i,rfl⟩
  · intro t ht
    obtain ⟨j,rfl⟩ := (real_diagonal_hasEigenvalue_iff d t).mp ht
    exact hmin j

theorem schur_quotient_takagi_minimum (A B Q : Matrix ι ι ℂ) (d : ι → ℝ)
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i) (i : ι) (hi : ∀ j, d j ≤ d i) :
    smallestRealEigenvalue (matrixSchur A B*A⁻¹) = 1-d i^2 := by
  have hs := schur_quotient_complex_similarity Q A B hQ
  rw [hA,hB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
  rw [← smallestRealEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q _ hQ),← hs]
  apply smallestRealEigenvalue_diagonal
  intro j
  nlinarith [hi j,hd j,hd i]

theorem schur_sub_minimum_mul_posSemidef [Nonempty ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B-(smallestRealEigenvalue (matrixSchur A B*A⁻¹):ℂ) • A).PosSemidef := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hi' (j : ι) : d j ≤ d i := hi j (Finset.mem_univ _)
  let s := smallestRealEigenvalue (matrixSchur A B*A⁻¹)
  have hs : s = 1-d i^2 := schur_quotient_takagi_minimum A B Q d hQ hQA hQB hd i hi'
  have hQM : Q*matrixSchur A B*Q.conjTranspose =
      Matrix.diagonal (fun j => ((1-d j^2:ℝ):ℂ)) := by
    rw [← matrixSchur_complex_congruence Q A B hQ,hQA,hQB,matrixSchur_one_real_diagonal]
  have hcong : Q*(matrixSchur A B-(s:ℂ) • A)*Q.conjTranspose =
      Matrix.diagonal (fun j => ((1-d j^2-s:ℝ):ℂ)) := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hQM,hQA]
    ext j k
    by_cases hjk : j=k
    · subst k; simp
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hjk]
  have hp : (Q*(matrixSchur A B-(s:ℂ) • A)*Q.conjTranspose).PosSemidef := by
    rw [hcong]
    apply Matrix.PosSemidef.diagonal
    intro j
    apply Complex.zero_le_real.mpr
    rw [hs]
    nlinarith [hi' j,hd j,hd i]
  exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (x := matrixSchur A B-(s:ℂ) • A) (Matrix.isUnit_iff_isUnit_det Q |>.mpr hQ)).mp hp

theorem schur_minimum_le_diagonal_ratio [Nonempty ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (i : ι) :
    smallestRealEigenvalue (matrixSchur A B*A⁻¹) ≤ (matrixSchur A B i i).re/(A i i).re := by
  have h := (Complex.nonneg_iff.mp
    ((schur_sub_minimum_mul_posSemidef hA hB).diag_nonneg (i := i))).1
  have hp := (Complex.pos_iff.mp (hA.diag_pos (i := i))).1
  apply (le_div_iff₀ hp).mpr
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  linarith

theorem schur_minimum_le_one [Nonempty ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    smallestRealEigenvalue (matrixSchur A B*A⁻¹) ≤ 1 := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  rw [schur_quotient_takagi_minimum A B Q d hQ hQA hQB hd i (fun j => hi j (Finset.mem_univ _))]
  nlinarith [sq_nonneg (d i)]

theorem schur_minimum_eq_one_iff [Nonempty ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    smallestRealEigenvalue (matrixSchur A B*A⁻¹) = 1 ↔ B = 0 := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  rw [schur_quotient_takagi_minimum A B Q d hQ hQA hQB hd i (fun j => hi j (Finset.mem_univ _))]
  constructor
  · intro h
    have hdi : d i = 0 := by nlinarith
    have hd0 : ∀ j, d j = 0 := fun j => le_antisymm (by simpa [hdi] using hi j (Finset.mem_univ _)) (hd j)
    have he : Q*B*Q.transpose = 0 := by rw [hQB]; simp [hd0]
    have hQt : IsUnit Q.transpose.det := by simpa using hQ
    have hzero := congrArg (fun M => Q⁻¹*M*Q.transpose⁻¹) he
    have hid : Q⁻¹*(Q*B*Q.transpose)*Q.transpose⁻¹ = B := by
      calc
        _ = (Q⁻¹*Q)*B*(Q.transpose*Q.transpose⁻¹) := by noncomm_ring
        _ = B := by rw [Matrix.nonsing_inv_mul _ hQ,Matrix.mul_nonsing_inv _ hQt]; simp
    rw [hid] at hzero
    simpa using hzero
  · intro h
    have hdiag : Matrix.diagonal (fun j => (d j:ℂ)) = 0 := by rw [← hQB,h]; simp
    have he := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hdiag
    have hi0 : d i = 0 := by simpa using he
    simp [hi0]

end PowerConvexity
