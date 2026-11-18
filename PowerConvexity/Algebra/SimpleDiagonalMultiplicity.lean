import PowerConvexity.Algebra.EigenvalueSchur
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A nonzero complementary minor excludes a repeated diagonal root

This is the multiplicity step missing from separation of distinct spectral
values alone. It applies to any invertible diagonalizing similarity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_root_unique_of_complement_det_ne_zero
    (K Q : Matrix ι ι ℂ) (i : ι) (z : ℂ)
    (hminor : (eigenvalueComplement K i z).det ≠ 0) (hQ : IsUnit Q.det)
    (d : ι → ℂ) (hdiag : Q*K*Q⁻¹ = Matrix.diagonal d)
    (j : ι) (hj : d j = z) : ∀ l, l ≠ j → d l ≠ z := by
  classical
  have hsub : (K-z • 1).submatrix
      (Subtype.val : {l : ι // l ≠ i} → ι) Subtype.val = eigenvalueComplement K i z := by
    ext l m
    simp [eigenvalueComplement,Matrix.submatrix_apply,Matrix.one_apply,Subtype.ext_iff]
  have hrank : Fintype.card {l : ι // l ≠ i} ≤ (K-z • 1).rank := by
    have h := Matrix.rank_submatrix_le (K-z • 1)
      (Subtype.val : {l : ι // l ≠ i} → ι) (Subtype.val : {l : ι // l ≠ i} → ι)
    rwa [hsub,Matrix.rank_of_det_ne_zero hminor] at h
  have hs : Q*(K-z • 1)*Q⁻¹ = Matrix.diagonal (fun l => d l-z) := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
      Matrix.mul_nonsing_inv Q hQ,hdiag]
    ext l m
    by_cases hlm : l=m
    · subst m; simp
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hlm]
  have hr : (K-z • 1).rank = Fintype.card {l : ι // d l-z ≠ 0} := by
    have hh := congrArg Matrix.rank hs
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Q⁻¹ _ (Q.isUnit_nonsing_inv_det hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det Q _ hQ,Matrix.rank_diagonal] at hh
    exact hh
  rw [hr] at hrank
  intro l hlj hl
  let f : {r : ι // d r-z ≠ 0} → {r : ι // r ≠ j} :=
    fun r => ⟨r.val,by intro he; exact r.property (by rw [he,hj,sub_self])⟩
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    exact congrArg (fun t : {r : ι // r ≠ j} => t.val) h
  have hnot : (⟨l,hlj⟩ : {r : ι // r ≠ j}) ∉ Set.range f := by
    rintro ⟨r,he⟩
    have hev : r.val=l := congrArg Subtype.val he
    exact r.property (by rw [hev,hl,sub_self])
  have hlt := Fintype.card_lt_of_injective_of_notMem f hf hnot
  simp only [Fintype.card_subtype_compl,Fintype.card_subtype_eq] at hrank hlt
  omega

end PowerConvexity
