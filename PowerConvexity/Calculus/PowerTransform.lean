import PowerConvexity.DependencyProbe
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The square-root transform in frozen manuscript §2.2

The real Hessian is the actual second Fréchet derivative.  The mixed and pure
complex Hessians are the actual CHS Wirtinger derivatives.  No formal jet is
substituted for a derivative, and no differential equation is required here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity

open CHS.Calculus

noncomputable def negativeSqrt (t : ℝ) : ℝ := -Real.sqrt (-t)

noncomputable def sqrtSlope (t : ℝ) : ℝ := 1 / (2 * Real.sqrt (-t))

noncomputable def powerTransform {E : Type*} (u : E → ℝ) : E → ℝ :=
  fun x => negativeSqrt (u x)

theorem sqrtSlope_pos {t : ℝ} (ht : t < 0) : 0 < sqrtSlope t := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.mpr (neg_pos.mpr ht)))

theorem hasDerivAt_negativeSqrt {t : ℝ} (ht : t < 0) :
    HasDerivAt negativeSqrt (sqrtSlope t) t := by
  have h := (((hasDerivAt_id t).neg).sqrt (ne_of_gt (neg_pos.mpr ht))).neg
  change HasDerivAt (fun s : ℝ => -Real.sqrt (-s)) (-(-1 / (2 * Real.sqrt (-t)))) t at h
  change HasDerivAt (fun s : ℝ => -Real.sqrt (-s)) (1 / (2 * Real.sqrt (-t))) t
  simpa only [neg_div, neg_neg] using h

theorem hasDerivAt_sqrtSlope {t : ℝ} (ht : t < 0) :
    HasDerivAt sqrtSlope (sqrtSlope t / (2 * (-t))) t := by
  have hs : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (neg_pos.mpr ht)
  have hn : Real.sqrt (-t) ≠ 0 := ne_of_gt hs
  have ht0 : t ≠ 0 := ne_of_lt ht
  have hsq : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt (le_of_lt (neg_pos.mpr ht))
  have h := (hasDerivAt_const t (1 : ℝ)).div
    ((((hasDerivAt_id t).neg).sqrt (ne_of_gt (neg_pos.mpr ht))).const_mul 2)
    (mul_ne_zero (by norm_num) hn)
  change HasDerivAt sqrtSlope
    ((0 * (2 * Real.sqrt (-t)) - 1 * (2 * (-1 / (2 * Real.sqrt (-t))))) /
      (2 * Real.sqrt (-t)) ^ 2) t at h
  convert h using 1
  dsimp only [sqrtSlope]
  field_simp [hn, ht0]
  nlinarith [hsq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem powerTransform_contDiffAt {u : E → ℝ} {x : E} {k : WithTop ℕ∞}
    (hu : ContDiffAt ℝ k u x) (hx : u x < 0) :
    ContDiffAt ℝ k (powerTransform u) x := by
  exact ((hu.neg).sqrt (ne_of_gt (neg_pos.mpr hx))).neg

theorem powerTransform_contDiffOn {u : E → ℝ} {U : Set E} {k : WithTop ℕ∞}
    (hu : ContDiffOn ℝ k u U) (hneg : ∀ x ∈ U, u x < 0) :
    ContDiffOn ℝ k (powerTransform u) U := by
  intro x hx
  exact ((hu x hx).neg.sqrt (ne_of_gt (neg_pos.mpr (hneg x hx)))).neg

theorem fderiv_powerTransform {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hx : u x < 0) :
    fderiv ℝ (powerTransform u) x = sqrtSlope (u x) • fderiv ℝ u x := by
  exact ((hasDerivAt_negativeSqrt hx).comp_hasFDerivAt x hu.hasFDerivAt).fderiv

theorem realHessian_powerTransform {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (v w : E) :
    realHessian (powerTransform u) x v w =
      sqrtSlope (u x) *
        (realHessian u x v w + (fderiv ℝ u x v * fderiv ℝ u x w) / (2 * (-u x))) := by
  have hu1 : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := (hasDerivAt_sqrtSlope hx).comp_hasFDerivAt x hu1.hasFDerivAt
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 u y :=
    (hu.of_le (m := 1) (by norm_num)).eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  have heq : fderiv ℝ (powerTransform u) =ᶠ[𝓝 x]
      (fun y => sqrtSlope (u y) • fderiv ℝ u y) := by
    filter_upwards [hnear, hneg] with y hy hyneg
    exact fderiv_powerTransform (hy.differentiableAt (by norm_num)) hyneg
  unfold realHessian
  have hprod := (hs.smul hdu.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => sqrtSlope (u y) • fderiv ℝ u y) x = _ at hprod
  rw [heq.fderiv_eq, hprod]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

/-- A first derivative with the manuscript's `1/2` Wirtinger normalization. -/
noncomputable def complexGradient {ι : Type*} (a b : ι → E) (u : E → ℝ)
    (x : E) (i : ι) : ℂ := dz (a i) (b i) (fun y => (u y : ℂ)) x

theorem complexGradient_real_entry {ι : Type*} {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (a b : ι → E) (i : ι) :
    complexGradient a b u x i = (2 : ℂ)⁻¹ *
      ((fderiv ℝ u x (a i) : ℂ) - Complex.I * (fderiv ℝ u x (b i) : ℂ)) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => (u y : ℂ)) _ x at h
  unfold complexGradient dz rd
  rw [h.fderiv]
  rfl

theorem complexGradient_conjugate {ι : Type*} {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (a b : ι → E) (i : ι) :
    complexGradient a (fun j => -b j) u x i = star (complexGradient a b u x i) := by
  rw [complexGradient_real_entry hu, complexGradient_real_entry hu]
  simp only [map_neg, Complex.ofReal_neg, star_mul, star_sub, star_inv₀, star_ofNat,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The mixed formula displayed at the beginning of §2.2. -/
theorem complexHessian_powerTransform {ι : Type*} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) (i j : ι) :
    complexHessian a b (powerTransform u) x i j =
      (sqrtSlope (u x) : ℂ) *
        (complexHessian a b u x i j +
          complexGradient a b u x i * star (complexGradient a b u x j) /
            ((2 * (-u x) : ℝ) : ℂ)) := by
  rw [complexHessian_real_entry (powerTransform_contDiffAt hu hx),
    complexHessian_real_entry hu]
  simp only [realHessian_powerTransform hu hx,
    complexGradient_real_entry (hu.differentiableAt (by norm_num)),
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div,
    star_mul, star_sub, star_inv₀, star_ofNat,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The pure formula displayed at the beginning of §2.2. -/
theorem pureHessian_powerTransform {ι : Type*} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) (i j : ι) :
    pureHessian a b (powerTransform u) x i j =
      (sqrtSlope (u x) : ℂ) *
        (pureHessian a b u x i j +
          complexGradient a b u x i * complexGradient a b u x j /
            ((2 * (-u x) : ℝ) : ℂ)) := by
  rw [pureHessian_real_entry (powerTransform_contDiffAt hu hx), pureHessian_real_entry hu]
  simp only [realHessian_powerTransform hu hx,
    complexGradient_real_entry (hu.differentiableAt (by norm_num)),
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div]
  ring_nf
  simp only [Complex.I_sq]
  ring

end PowerConvexity
