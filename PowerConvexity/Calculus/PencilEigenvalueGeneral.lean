import PowerConvexity.Calculus.PencilEigenvalueTwo
import PowerConvexity.Calculus.SimpleEigenvalueDerivatives
import PowerConvexity.Algebra.EigenvalueSchur

/-! # Actual derivatives of a general finite-dimensional characteristic pencil

These exact formulas retain lambda and its gradient; the zero-contact case
is a specialization, not an assumed differentiation rule.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pencil_schur_root_eventually
    {M A : E → Matrix ι ι ℂ} {ell : E → ℂ} {x : E}
    (hM : ∀ j k, ContDiffAt ℝ 2 (fun y => M y j k) x)
    (hA : ∀ j k, ContDiffAt ℝ 2 (fun y => A y j k) x)
    (hell : ContDiffAt ℝ 2 ell x) (i : ι) (d : ι → ℂ)
    (hI : A x = 1) (hdiag : M x = Matrix.diagonal d)
    (hvalue : ell x = d i) (hgap : ∀ j, j ≠ i → d j ≠ d i)
    (hroot : ∀ᶠ y in 𝓝 x, (M y - ell y • A y).det = 0) :
    ∀ᶠ y in 𝓝 x, eigenvalueSchur (M y - ell y • A y) i 0 = 0 := by
  let P : E → Matrix ι ι ℂ := fun y => M y - ell y • A y
  have hP (j k : ι) : ContDiffAt ℝ 2 (fun y => P y j k) x :=
    (hM j k).sub (hell.mul (hA j k))
  have hD : P x = Matrix.diagonal (fun j => d j - d i) := by
    ext j k
    by_cases hjk : j = k
    · subst k; simp [P, hI, hdiag, hvalue]
    · simp [P, hI, hdiag, Matrix.diagonal_apply, Matrix.one_apply, hjk]
  have hd : (eigenvalueComplement (P x) i 0).det ≠ 0 := by
    rw [hD, eigenvalueComplement_diagonal, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simpa using sub_ne_zero.mpr (hgap j j.property)
  have hc (j k : {j : ι // j ≠ i}) :
      ContDiffAt ℝ 2 (fun y => eigenvalueComplement (P y) i 0 j k) x := by
    simpa [eigenvalueComplement] using hP j k
  have hn := (field_det_contDiffAt hc).continuousAt.eventually_ne hd
  filter_upwards [hn, hroot] with y hy hry
  have he := det_sub_scalar_eq_complement_mul_schur (P y) i 0 hy
  simp only [zero_smul, sub_zero] at he
  change (P y).det = 0 at hry
  rw [hry] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hy

theorem generalized_eigenvalue_dz_mixed
    {M A : E → Matrix ι ι ℂ} {ell : E → ℂ} {x : E}
    (hM : ∀ j k, ContDiffAt ℝ 2 (fun y => M y j k) x)
    (hA : ∀ j k, ContDiffAt ℝ 2 (fun y => A y j k) x)
    (hell : ContDiffAt ℝ 2 ell x) (i : ι) (d : ι → ℂ)
    (hI : A x = 1) (hdiag : M x = Matrix.diagonal d)
    (hvalue : ell x = d i) (hgap : ∀ j, j ≠ i → d j ≠ d i)
    (hroot : ∀ᶠ y in 𝓝 x, (M y - ell y • A y).det = 0)
    (v w s t : E) :
    dz v w ell x = dz v w (fun y => M y i i) x -
      ell x * dz v w (fun y => A y i i) x ∧
    dz s t (dz v w ell) x =
      dz s t (dz v w (fun y => M y i i)) x -
      ell x * dz s t (dz v w (fun y => A y i i)) x -
      dz v w ell x * dz s t (fun y => A y i i) x -
      dz s t ell x * dz v w (fun y => A y i i) x +
      ∑ j : {j : ι // j ≠ i},
        ((dz v w (fun y => M y i j) x - ell x * dz v w (fun y => A y i j) x) *
          (dz s t (fun y => M y j i) x - ell x * dz s t (fun y => A y j i) x) +
         (dz s t (fun y => M y i j) x - ell x * dz s t (fun y => A y i j) x) *
          (dz v w (fun y => M y j i) x - ell x * dz v w (fun y => A y j i) x)) /
          (d i - d j) := by
  let P : E → Matrix ι ι ℂ := fun y => M y - ell y • A y
  have hP (j k : ι) : ContDiffAt ℝ 2 (fun y => P y j k) x :=
    (hM j k).sub (hell.mul (hA j k))
  have hD : P x = Matrix.diagonal (fun j => d j - d i) := by
    ext j k
    by_cases hjk : j = k
    · subst k; simp [P, hI, hdiag, hvalue]
    · simp [P, hI, hdiag, Matrix.diagonal_apply, Matrix.one_apply, hjk]
  have hgapP (j : ι) (hj : j ≠ i) : d j - d i ≠ d i - d i := by
    simpa using sub_ne_zero.mpr (hgap j hj)
  have he := simple_schur_root_derivatives hP contDiffAt_const i
    (fun j => d j - d i) hD (by simp) hgapP
    (pencil_schur_root_eventually hM hA hell i d hI hdiag hvalue hgap hroot)
    v w s t
  dsimp only [P, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at he
  have hz : dz v w (fun _ : E => (0 : ℂ)) = fun _ => 0 := by
    funext y
    exact dz_const v w 0 y
  simp only [hz, dz_const] at he
  have hd1 := pencil_entry_dz ((hM i i).differentiableAt (by norm_num))
    ((hA i i).differentiableAt (by norm_num)) (hell.differentiableAt (by norm_num)) v w
  have hd2 := pencil_entry_mixed (hM i i) (hA i i) hell v w s t
  rw [hI] at hd1 hd2
  simp only [Matrix.one_apply_eq, mul_one] at hd1 hd2
  constructor
  · linear_combination he.1 + hd1
  · have hsum :
        (∑ j : {j : ι // j ≠ i},
          (dz v w (fun y => M y i j - ell y * A y i j) x *
            dz s t (fun y => M y j i - ell y * A y j i) x +
           dz s t (fun y => M y i j - ell y * A y i j) x *
            dz v w (fun y => M y j i - ell y * A y j i) x) /
            ((d i - d i) - (d j - d i))) =
        ∑ j : {j : ι // j ≠ i},
          ((dz v w (fun y => M y i j) x - ell x * dz v w (fun y => A y i j) x) *
            (dz s t (fun y => M y j i) x - ell x * dz s t (fun y => A y j i) x) +
           (dz s t (fun y => M y i j) x - ell x * dz s t (fun y => A y i j) x) *
            (dz v w (fun y => M y j i) x - ell x * dz v w (fun y => A y j i) x)) /
            (d i - d j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [pencil_entry_dz ((hM i j).differentiableAt (by norm_num))
          ((hA i j).differentiableAt (by norm_num)) (hell.differentiableAt (by norm_num)),
        pencil_entry_dz ((hM j i).differentiableAt (by norm_num))
          ((hA j i).differentiableAt (by norm_num)) (hell.differentiableAt (by norm_num)),
        hI, Matrix.one_apply_ne j.property, Matrix.one_apply_ne (Ne.symm j.property),
        mul_zero, sub_zero]
      congr 1
      ring
    linear_combination he.2 + hd2 + hsum

end PowerConvexity
