import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Actual generalized Rayleigh minimum and unit-vector contacts -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Matrix
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def generalizedRayleigh (M A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ (M *ᵥ v)).re / (star v ⬝ᵥ (A *ᵥ v)).re

theorem schur_minimum_hasEigenvalue {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    Module.End.HasEigenvalue (matrixSchur A B*A⁻¹).toLin'
      (smallestRealEigenvalue (matrixSchur A B*A⁻¹):ℂ) := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  rw [schur_quotient_takagi_minimum A B Q d hQ hQA hQB hd i (fun j => hi j (Finset.mem_univ _))]
  have hs := schur_quotient_complex_similarity Q A B hQ
  rw [hQA,hQB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
  apply (hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q _ hQ) _).mp
  rw [← hs]
  exact (real_diagonal_hasEigenvalue_iff _ _).mpr ⟨i,rfl⟩

theorem schur_minimum_le_generalizedRayleigh {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) {v : ι → ℂ} (hv : v ≠ 0) :
    smallestRealEigenvalue (matrixSchur A B*A⁻¹) ≤ generalizedRayleigh (matrixSchur A B) A v := by
  have h := (Complex.nonneg_iff.mp
    ((schur_sub_minimum_mul_posSemidef hA hB).dotProduct_mulVec_nonneg v)).1
  have hp := (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hv)).1
  unfold generalizedRayleigh
  apply (le_div_iff₀ hp).mpr
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,
    smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at h
  linarith

theorem generalizedRayleigh_eq_of_eigenvector {A M : Matrix ι ι ℂ}
    (hA : A.PosDef) {v : ι → ℂ} (hv : v ≠ 0) (s : ℝ)
    (he : M*ᵥv = (s:ℂ) • (A*ᵥv)) : generalizedRayleigh M A v = s := by
  have hp := (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hv)).1
  unfold generalizedRayleigh
  rw [he,dotProduct_smul]
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_div_cancel_right₀ _ hp.ne'

theorem exists_unit_generalizedRayleigh_minimum {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    ∃ v : ι → ℂ, ‖v‖ = 1 ∧ generalizedRayleigh (matrixSchur A B) A v =
      smallestRealEigenvalue (matrixSchur A B*A⁻¹) := by
  let s := smallestRealEigenvalue (matrixSchur A B*A⁻¹)
  obtain ⟨z,hz,hz0⟩ := (schur_minimum_hasEigenvalue hA hB).exists_hasEigenvector
  have he : (matrixSchur A B*A⁻¹)*ᵥz = (s:ℂ) • z := Module.End.mem_eigenspace_iff.mp hz
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  let v := A⁻¹*ᵥz
  have hav : A*ᵥv = z := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hAu,Matrix.one_mulVec]
  have hv : v ≠ 0 := by
    intro h
    apply hz0
    rw [← hav,h,Matrix.mulVec_zero]
  have hmv : matrixSchur A B*ᵥv = (s:ℂ) • (A*ᵥv) := by
    rw [hav]
    change matrixSchur A B *ᵥ (A⁻¹ *ᵥ z) = (s:ℂ) • z
    rw [Matrix.mulVec_mulVec,he]
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  refine ⟨w,hw,generalizedRayleigh_eq_of_eigenvector hA (by intro h; simpa [h] using hw) s ?_⟩
  dsimp only [w]
  rw [Matrix.mulVec_smul,hmv,Matrix.mulVec_smul,smul_comm]

end PowerConvexity
