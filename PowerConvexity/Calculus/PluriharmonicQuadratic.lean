import PowerConvexity.Calculus.RealHessianRules
import PowerConvexity.Calculus.CoordinateCovariance

/-!
# Actual centered pluriharmonic rank-one quadratic perturbations

The normalization is q = Re (ell (z-c))^2.  Thus q_ij = ell(a_i) ell(a_j),
whereas its real Hessian is 2 Re (ell(v) ell(w)).  Values and first derivatives
vanish at c.  No abstract jet is substituted for this concrete polynomial.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

noncomputable def realPartSquare (ell : E →L[ℝ] ℂ) (c : E) (y : E) : ℝ :=
  ((ell (y-c))^2).re

theorem realPartSquare_contDiff (ell : E →L[ℝ] ℂ) (c : E) (k : ℕ∞ω) :
    ContDiff ℝ k (realPartSquare ell c) :=
  Complex.reCLM.contDiff.comp ((ell.contDiff.comp (contDiff_id.sub contDiff_const)).pow 2)

theorem realPartSquare_center (ell : E →L[ℝ] ℂ) (c : E) : realPartSquare ell c c = 0 := by
  simp [realPartSquare]

theorem realPartSquare_hasFDerivAt_center (ell : E →L[ℝ] ℂ) (c : E) :
    HasFDerivAt (realPartSquare ell c) (0 : E →L[ℝ] ℝ) c := by
  have hl : HasFDerivAt (fun y => ell (y-c)) ell c := by
    convert ell.hasFDerivAt.comp c ((hasFDerivAt_id c).sub_const c) using 1 <;> try rfl
    all_goals ext v <;> simp
  have hh : HasFDerivAt (fun y => ell (y-c) * ell (y-c)) (0 : E →L[ℝ] ℂ) c := by
    convert hl.mul hl using 1 <;> try rfl
    all_goals ext v <;> simp
  convert Complex.reCLM.hasFDerivAt.comp c hh using 1 <;> try rfl
  funext y
  simp [realPartSquare, pow_two]

theorem realHessian_realCLM_sq (ell : E →L[ℝ] ℝ) (x v w : E) :
    realHessian (fun y => (ell y)^2) x v w = 2 * ell v * ell w := by
  have he : (fun y => (ell y)^2) = (fun y => ‖ell y‖^2) := by
    funext y
    simp only [Real.norm_eq_abs, sq_abs]
  rw [he, realHessian_norm_sq_comp]
  simp only [Real.inner_apply]
  ring

theorem realHessian_realCLM_centered_sq (ell : E →L[ℝ] ℝ) (c x v w : E) :
    realHessian (fun y => (ell (y-c))^2) x v w = 2 * ell v * ell w := by
  have he : (fun y => (ell (y-c))^2) =
      (fun y => (ell (-c + (ContinuousLinearMap.id ℝ E) y))^2) := by
    funext y
    simp only [ContinuousLinearMap.id_apply, sub_eq_add_neg, add_comm]
  rw [he, realHessian_comp_affine (ContinuousLinearMap.id ℝ E) (-c)
    (ell.contDiff.pow 2).contDiffAt]
  exact realHessian_realCLM_sq ell _ _ _

theorem realHessian_realPartSquare (ell : E →L[ℝ] ℂ) (c x v w : E) :
    realHessian (realPartSquare ell c) x v w = 2 * (ell v * ell w).re := by
  let R := Complex.reCLM.comp ell
  let J := Complex.imCLM.comp ell
  have he : realPartSquare ell c = (fun y => (R (y-c))^2 - (J (y-c))^2) := by
    funext y
    simp only [realPartSquare, pow_two, Complex.mul_re, R, J,
      ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  have hR : ContDiffAt ℝ 2 (fun y => (R (y-c))^2) x :=
    ((R.contDiff.comp (contDiff_id.sub (contDiff_const (c := c)))).pow 2).contDiffAt
  have hJ : ContDiffAt ℝ 2 (fun y => (J (y-c))^2) x :=
    ((J.contDiff.comp (contDiff_id.sub (contDiff_const (c := c)))).pow 2).contDiffAt
  rw [he, realHessian_sub_at hR hJ]
  simp only [sub_apply]
  rw [realHessian_realCLM_centered_sq R c x v w,
    realHessian_realCLM_centered_sq J c x v w]
  simp only [R, J, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.mul_re]
  ring

/-- Complex-linearity of ell is recorded in the actual constant directions. -/
theorem realPartSquare_mixedHessian_zero (ell : E →L[ℝ] ℂ) (c : E)
    (a b : ι → E) (hJ : ∀ i, ell (b i) = Complex.I * ell (a i)) (x : E) :
    complexHessian a b (realPartSquare ell c) x = 0 := by
  ext i j
  rw [complexHessian_real_entry (realPartSquare_contDiff ell c 2).contDiffAt]
  simp only [realHessian_realPartSquare, hJ, Matrix.zero_apply,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem realPartSquare_pureHessian (ell : E →L[ℝ] ℂ) (c : E)
    (a b : ι → E) (hJ : ∀ i, ell (b i) = Complex.I * ell (a i)) (x : E) :
    pureHessian a b (realPartSquare ell c) x = fun i j => ell (a i) * ell (a j) := by
  ext i j
  rw [pureHessian_real_entry (realPartSquare_contDiff ell c 2).contDiffAt]
  simp only [realHessian_realPartSquare, hJ]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat] <;>
    norm_num <;> ring

theorem abs_realPartSquare_le (ell : E →L[ℝ] ℂ) (c y : E) :
    |realPartSquare ell c y| ≤ ‖ell‖^2 * ‖y-c‖^2 := by
  have h := Complex.abs_re_le_norm ((ell (y-c))^2)
  rw [norm_pow] at h
  have hop := ell.le_opNorm (y-c)
  calc
    |realPartSquare ell c y| ≤ ‖ell (y-c)‖^2 := h
    _ ≤ (‖ell‖ * ‖y-c‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = _ := by ring

end PowerConvexity
