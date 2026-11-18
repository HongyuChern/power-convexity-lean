import PowerConvexity.Calculus.SimpleEigenvalueSchur
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # The scalar Schur root is an actual eigenvalue -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distinguishedIndexEquiv (i : ι) : Unit ⊕ {j : ι // j ≠ i} ≃ ι where
  toFun := Sum.elim (fun _ => i) Subtype.val
  invFun j := if h : j = i then Sum.inl () else Sum.inr ⟨j,h⟩
  left_inv := by
    rintro (⟨⟩|⟨j,hj⟩)
    · simp
    · simp [hj]
  right_inv := by intro j; by_cases h : j = i <;> simp [h]

theorem det_sub_scalar_eq_complement_mul_schur (K : Matrix ι ι ℂ) (i : ι) (z : ℂ)
    (hd : (eigenvalueComplement K i z).det ≠ 0) :
    (K-z • 1).det = (eigenvalueComplement K i z).det * eigenvalueSchur K i z := by
  let e := distinguishedIndexEquiv i
  let D := eigenvalueComplement K i z
  let : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hd)
  have he : (K-z • 1).submatrix e e = Matrix.fromBlocks
      (fun _ _ : Unit => K i i-z)
      (fun (_ : Unit) (j : {j : ι // j ≠ i}) => K i j)
      (fun (j : {j : ι // j ≠ i}) (_ : Unit) => K j i) D := by
    ext (j|j) (k|k)
    · simp [e, distinguishedIndexEquiv]
    · simp [e, distinguishedIndexEquiv, Ne.symm k.property]
    · simp [e, distinguishedIndexEquiv, j.property]
    · simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        distinguishedIndexEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, e]
      change K j k-z*(if j.val = k.val then 1 else 0) =
        K j k-z*(if j = k then 1 else 0)
      simp only [Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e, he, Matrix.det_fromBlocks₂₂,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Unit)]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul, eigenvalueSchur]
  rw [Finset.sum_comm]

theorem matrix_hasEigenvalue_iff_det_sub_eq_zero (K : Matrix ι ι ℂ) (z : ℂ) :
    Module.End.HasEigenvalue K.toLin' z ↔ (K-z • 1).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨v,hv,hv0⟩ := h.exists_hasEigenvector
    refine ⟨v,hv0,?_⟩
    have he : K.mulVec v = z • v := Module.End.mem_eigenspace_iff.mp hv
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_self]
  · rintro ⟨v,hv0,hv⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,hv0⟩
    change K.mulVec v = z • v
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero] using hv

theorem eigenvalueSchur_eq_zero_iff (K : Matrix ι ι ℂ) (i : ι) (z : ℂ)
    (hd : (eigenvalueComplement K i z).det ≠ 0) :
    eigenvalueSchur K i z = 0 ↔ Module.End.HasEigenvalue K.toLin' z := by
  rw [matrix_hasEigenvalue_iff_det_sub_eq_zero,
    det_sub_scalar_eq_complement_mul_schur K i z hd, mul_eq_zero]
  exact (or_iff_right hd).symm

end PowerConvexity
