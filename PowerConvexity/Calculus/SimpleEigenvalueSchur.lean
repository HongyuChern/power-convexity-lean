import PowerConvexity.Calculus.MatrixInverse
import PowerConvexity.Calculus.ScalarSecondCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # A local simple eigenvalue from an actual Schur equation

The complementary minor is invertible at a diagonal matrix with a simple
distinguished eigenvalue. Its scalar Schur complement gives an actual smooth
root by the implicit function theorem, without differentiating eigenvectors.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def eigenvalueComplement (K : Matrix ι ι ℂ) (i : ι) (z : ℂ) :
    Matrix {j : ι // j ≠ i} {j : ι // j ≠ i} ℂ :=
  K.submatrix Subtype.val Subtype.val - z • 1

noncomputable def eigenvalueSchur (K : Matrix ι ι ℂ) (i : ι) (z : ℂ) : ℂ :=
  K i i-z-∑ j : {j : ι // j ≠ i}, ∑ k : {j : ι // j ≠ i},
    K i j * (eigenvalueComplement K i z)⁻¹ j k * K k i

theorem eigenvalueComplement_diagonal (d : ι → ℂ) (i : ι) (z : ℂ) :
    eigenvalueComplement (Matrix.diagonal d) i z =
      Matrix.diagonal (fun j : {j : ι // j ≠ i} => d j-z) := by
  ext j k
  by_cases h : j = k
  · subst k
    simp [eigenvalueComplement]
  · have hv : j.val ≠ k.val := fun he => h (Subtype.ext he)
    simp [eigenvalueComplement, h, hv]

theorem eigenvalueComplement_diagonal_det_ne_zero (d : ι → ℂ) (i : ι)
    (hgap : ∀ j, j ≠ i → d j ≠ d i) :
    (eigenvalueComplement (Matrix.diagonal d) i (d i)).det ≠ 0 := by
  rw [eigenvalueComplement_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hgap j j.property)

theorem eigenvalueComplement_diagonal_inverse (d : ι → ℂ) (i : ι)
    (hgap : ∀ j, j ≠ i → d j ≠ d i) :
    (eigenvalueComplement (Matrix.diagonal d) i (d i))⁻¹ =
      Matrix.diagonal (fun j : {j : ι // j ≠ i} => (d j-d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [eigenvalueComplement_diagonal, Matrix.diagonal_mul_diagonal]
  have he : (fun j : {j : ι // j ≠ i} => (d j-d i)*(d j-d i)⁻¹) = 1 := by
    funext j
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hgap j j.property))
  rw [he]
  exact Matrix.diagonal_one

theorem eigenvalueSchur_diagonal (d : ι → ℂ) (i : ι) (z : ℂ) :
    eigenvalueSchur (Matrix.diagonal d) i z = d i-z := by
  unfold eigenvalueSchur
  have hz (j : {j : ι // j ≠ i}) : Matrix.diagonal d i j = 0 := by
    exact Matrix.diagonal_apply_ne d (Ne.symm j.property)
  simp only [hz, zero_mul, Finset.sum_const_zero, sub_zero, Matrix.diagonal_apply_eq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eigenvalueSchur_contDiffAt {K : E → Matrix ι ι ℂ} {x : E} {z : ℂ}
    {r : ℕ∞ω} (hK : ∀ j k, ContDiffAt ℝ r (fun y => K y j k) x) (i : ι)
    (hd : (eigenvalueComplement (K x) i z).det ≠ 0) :
    ContDiffAt ℝ r (fun p : E × ℂ => eigenvalueSchur (K p.1) i p.2) (x,z) := by
  have hc (j k : {j : ι // j ≠ i}) : ContDiffAt ℝ r
      (fun p : E × ℂ => eigenvalueComplement (K p.1) i p.2 j k) (x,z) :=
    ((hK j k).comp (x,z) contDiffAt_fst).sub (contDiffAt_snd.mul contDiffAt_const)
  have hi := field_inverse_contDiffAt_of_det_ne_zero hc hd
  apply (((hK i i).comp (x,z) contDiffAt_fst).sub contDiffAt_snd).sub
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro k _
  exact (((hK i j.val).comp (x,z) contDiffAt_fst).mul (hi j k)).mul
    ((hK k.val i).comp (x,z) contDiffAt_fst)

theorem exists_contDiff_simple_schur_root [CompleteSpace E]
    {K : E → Matrix ι ι ℂ} {x : E} (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (i : ι) (d : ι → ℂ) (hdiag : K x = Matrix.diagonal d)
    (hgap : ∀ j, j ≠ i → d j ≠ d i) :
    ∃ ell : E → ℂ, ContDiffAt ℝ 2 ell x ∧ ell x = d i ∧
      (∀ᶠ y in 𝓝 x, eigenvalueSchur (K y) i (ell y) = 0) ∧
      (∀ᶠ p : E × ℂ in 𝓝 (x,d i),
        eigenvalueSchur (K p.1) i p.2 = 0 ↔ ell p.1 = p.2) := by
  let F : E × ℂ → ℂ := fun p => eigenvalueSchur (K p.1) i p.2
  have hd : (eigenvalueComplement (K x) i (d i)).det ≠ 0 := by
    rw [hdiag]
    exact eigenvalueComplement_diagonal_det_ne_zero d i hgap
  have hc : ContDiffAt ℝ 2 F (x,d i) := eigenvalueSchur_contDiffAt hK i hd
  have hF : (fun z : ℂ => F (x,z)) = fun z => d i-z := by
    funext z
    simp only [F, hdiag, eigenvalueSchur_diagonal]
  have hpartial : fderiv ℝ F (x,d i) ∘L ContinuousLinearMap.inr ℝ E ℂ =
      -ContinuousLinearMap.id ℝ ℂ := by
    have hin : HasFDerivAt (fun z : ℂ => (x,z)) (ContinuousLinearMap.inr ℝ E ℂ) (d i) :=
      (hasFDerivAt_const x (d i)).prodMk (hasFDerivAt_id (d i))
    have hcomp := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (d i) hin
    change HasFDerivAt (fun z : ℂ => F (x,z))
      (fderiv ℝ F (x,d i) ∘L ContinuousLinearMap.inr ℝ E ℂ) (d i) at hcomp
    rw [hF] at hcomp
    have href := (hasFDerivAt_const (𝕜 := ℝ) (d i) (d i)).sub (hasFDerivAt_id (𝕜 := ℝ) (d i))
    simpa only [zero_sub] using hcomp.unique href
  have hinv : (fderiv ℝ F (x,d i) ∘L ContinuousLinearMap.inr ℝ E ℂ).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.neg ℝ, rfl⟩
  have hn : (2 : ℕ∞ω) ≠ 0 := by norm_num
  refine ⟨hc.implicitFunction hn hinv, hc.contDiffAt_implicitFunction hn hinv,
    hc.implicitFunction_apply_self hn hinv, ?_, ?_⟩
  · simpa only [F, hdiag, eigenvalueSchur_diagonal, sub_self] using
      hc.eventually_apply_implicitFunction hn hinv
  · simpa only [F, hdiag, eigenvalueSchur_diagonal, sub_self] using
      hc.eventually_apply_eq_iff_implicitFunction hn hinv

end PowerConvexity
