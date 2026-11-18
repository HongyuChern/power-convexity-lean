import PowerConvexity.Calculus.SimpleEigenvalueSchur
import PowerConvexity.Calculus.NormComplement

/-! # General-dimensional first and mixed second simple-root formulas

All derivatives are actual constant-direction Wirtinger derivatives. The
complement inverse is differentiated only inside products whose outer factors
vanish at the diagonal base point. Consequently no inverse derivative survives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_mixed_sum_at {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, ContDiffAt ℝ 2 (f j) x) (a b c d : E) :
    dz c d (dz a b (fun y => ∑ j, f j y)) x =
      ∑ j, dz c d (dz a b (f j)) x := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ j, ContDiffAt ℝ 1 (f j) y :=
    eventually_all.mpr fun j => ((hf j).of_le (by norm_num : (1:ℕ∞ω) ≤ 2)).eventually (by simp)
  have he : dz a b (fun y => ∑ j, f j y) =ᶠ[𝓝 x] fun y => ∑ j, dz a b (f j) y := by
    filter_upwards [hn] with y hy
    exact dz_sum_at (fun j => (hy j).differentiableAt (by norm_num)) a b
  rw [dz_congr_nhds he]
  exact dz_sum_at (fun j => (dz_contDiffAt_one (hf j) a b).differentiableAt (by norm_num)) c d

theorem dz_triple_zero_at {f g h : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hfx : f x = 0) (hhx : h x = 0) (a b : E) :
    dz a b (fun y => f y*g y*h y) x = 0 := by
  rw [dz_mul_at (f := fun y => f y*g y) (hf.mul hg) hh]
  simp only [hfx, hhx, zero_mul, mul_zero, add_zero]

theorem dz_mixed_triple_zero_at {f g h : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hh : ContDiffAt ℝ 2 h x) (hfx : f x = 0) (hhx : h x = 0) (a b c d : E) :
    dz c d (dz a b (fun y => f y*g y*h y)) x =
      g x * (dz a b f x*dz c d h x+dz c d f x*dz a b h x) := by
  rw [dz_mixed_mul_at (hf.mul hg) hh,
    dz_mul_at (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num)),
    dz_mul_at (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
  simp only [hfx, hhx, zero_mul, mul_zero, add_zero]
  ring

theorem simple_schur_root_derivatives {K : E → Matrix ι ι ℂ} {ell : E → ℂ} {x : E}
    (hK : ∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x)
    (hell : ContDiffAt ℝ 2 ell x) (i : ι) (d : ι → ℂ)
    (hdiag : K x = Matrix.diagonal d) (hellx : ell x = d i)
    (hgap : ∀ j, j ≠ i → d j ≠ d i)
    (hroot : ∀ᶠ y in 𝓝 x, eigenvalueSchur (K y) i (ell y) = 0)
    (a b c e : E) :
    dz a b ell x = dz a b (fun y => K y i i) x ∧
    dz c e (dz a b ell) x = dz c e (dz a b (fun y => K y i i)) x +
      ∑ j : {j : ι // j ≠ i},
        (dz a b (fun y => K y i j) x * dz c e (fun y => K y j i) x +
          dz c e (fun y => K y i j) x * dz a b (fun y => K y j i) x) / (d i-d j) := by
  let J := {j : ι // j ≠ i}
  let G : E → Matrix J J ℂ := fun y => (eigenvalueComplement (K y) i (ell y))⁻¹
  let R : E → ℂ := fun y => ∑ j : J, ∑ k : J, K y i j * G y j k * K y k i
  have hcomp (j k : J) : ContDiffAt ℝ 2
      (fun y => eigenvalueComplement (K y) i (ell y) j k) x :=
    (hK j k).sub (hell.mul contDiffAt_const)
  have hdet : (eigenvalueComplement (K x) i (ell x)).det ≠ 0 := by
    rw [hdiag,hellx]
    exact eigenvalueComplement_diagonal_det_ne_zero d i hgap
  have hG (j k : J) : ContDiffAt ℝ 2 (fun y => G y j k) x :=
    field_inverse_contDiffAt_of_det_ne_zero hcomp hdet j k
  have ht (j k : J) : ContDiffAt ℝ 2 (fun y => K y i j * G y j k * K y k i) x :=
    ((hK i j).mul (hG j k)).mul (hK k i)
  have hR : ContDiffAt ℝ 2 R x := ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ => ht j k
  have hrow (j : J) : K x i j = 0 := by rw [hdiag]; exact Matrix.diagonal_apply_ne d (Ne.symm j.property)
  have hcol (j : J) : K x j i = 0 := by rw [hdiag]; exact Matrix.diagonal_apply_ne d j.property
  have hGe : G x = Matrix.diagonal (fun j : J => (d j-d i)⁻¹) := by
    dsimp only [G]
    rw [hdiag,hellx]
    exact eigenvalueComplement_diagonal_inverse d i hgap
  have heq : (fun y => K y i i-ell y) =ᶠ[𝓝 x] R := by
    filter_upwards [hroot] with y hy
    exact sub_eq_zero.mp hy
  have hR1 : dz a b R x = 0 := by
    rw [show R = (fun y => ∑ j : J, ∑ k : J, K y i j * G y j k * K y k i) from rfl,
      dz_sum_at (fun j => (ContDiffAt.sum (fun k _ => ht j k)).differentiableAt (by norm_num))]
    apply Finset.sum_eq_zero
    intro j _
    rw [dz_sum_at (fun k => (ht j k).differentiableAt (by norm_num))]
    apply Finset.sum_eq_zero
    intro k _
    exact dz_triple_zero_at ((hK i j).differentiableAt (by norm_num))
      ((hG j k).differentiableAt (by norm_num)) ((hK k i).differentiableAt (by norm_num))
      (hrow j) (hcol k) a b
  have hR2 : dz c e (dz a b R) x =
      ∑ j : J, (d j-d i)⁻¹ *
        (dz a b (fun y => K y i j) x * dz c e (fun y => K y j i) x +
          dz c e (fun y => K y i j) x * dz a b (fun y => K y j i) x) := by
    rw [show R = (fun y => ∑ j : J, ∑ k : J, K y i j * G y j k * K y k i) from rfl,
      dz_mixed_sum_at (fun j => ContDiffAt.sum (fun k _ => ht j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [dz_mixed_sum_at (fun k => ht j k)]
    simp_rw [dz_mixed_triple_zero_at (hK i j) (hG j _) (hK _ i) (hrow j) (hcol _), hGe]
    simp [Matrix.diagonal_apply, ite_mul]
  constructor
  · have h := dz_congr_nhds heq a b
    rw [dz_sub_at ((hK i i).differentiableAt (by norm_num))
      (hell.differentiableAt (by norm_num)), hR1] at h
    exact (sub_eq_zero.mp h).symm
  · have h := dz_dz_congr_nhds heq a b c e
    rw [dz_mixed_sub_at (hK i i) hell, hR2] at h
    have hs : -(∑ j : J, (d j-d i)⁻¹ *
        (dz a b (fun y => K y i j) x * dz c e (fun y => K y j i) x +
          dz c e (fun y => K y i j) x * dz a b (fun y => K y j i) x)) =
      ∑ j : J, (dz a b (fun y => K y i j) x * dz c e (fun y => K y j i) x +
          dz c e (fun y => K y i j) x * dz a b (fun y => K y j i) x) / (d i-d j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [show d i-d j = -(d j-d i) by ring, div_neg, div_eq_mul_inv]
      ring
    rw [← hs]
    linear_combination -h

end PowerConvexity
