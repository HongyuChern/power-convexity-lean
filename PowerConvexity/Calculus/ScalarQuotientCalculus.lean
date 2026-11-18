import PowerConvexity.Calculus.ScalarSecondCalculus

/-! # Actual inverse and quotient rules in constant Wirtinger directions -/

set_option autoImplicit false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_inv_at {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hx : f x ≠ 0) (a b : E) :
    dz a b (fun y => (f y)⁻¹) x = -dz a b f x / (f x)^2 := by
  have hi : DifferentiableAt ℝ (fun y => (f y)⁻¹) x := hf.inv hx
  have hn : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.eventually_ne hx
  have he : (fun y => f y * (f y)⁻¹) =ᶠ[𝓝 x] fun _ => (1 : ℂ) :=
    hn.mono fun y hy => mul_inv_cancel₀ hy
  have hz := dz_of_eventually_const he a b
  have hp := dz_mul_at hf hi a b
  rw [hp] at hz
  apply (eq_div_iff (pow_ne_zero 2 hx)).mpr
  field_simp at hz
  simp only [one_div] at hz
  linear_combination hz

theorem dz_div_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hx : g x ≠ 0) (a b : E) :
    dz a b (fun y => f y / g y) x =
      (dz a b f x * g x - f x * dz a b g x) / (g x)^2 := by
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x := hg.inv hx
  have hp := dz_mul_at hf hi a b
  simp only [div_eq_mul_inv]
  rw [hp, dz_inv_at hg hx]
  field_simp
  ring

theorem dz_mixed_inv_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hx : f x ≠ 0) (a b c d : E) :
    dz c d (dz a b (fun y => (f y)⁻¹)) x =
      (2 * dz a b f x * dz c d f x - f x * dz c d (dz a b f) x) / (f x)^3 := by
  have hi : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) x := hf.inv hx
  have hd := hf.differentiableAt (by norm_num)
  have hn : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.eventually_ne hx
  have he : (fun y => f y * (f y)⁻¹) =ᶠ[𝓝 x] fun _ => (1 : ℂ) :=
    hn.mono fun y hy => mul_inv_cancel₀ hy
  have hz := dz_dz_of_eventually_const he c d a b
  rw [dz_mixed_mul_at hf hi, dz_inv_at hd hx, dz_inv_at hd hx] at hz
  apply (eq_div_iff (pow_ne_zero 3 hx)).mpr
  field_simp at hz
  simp only [one_div] at hz
  linear_combination hz

theorem dz_mixed_div_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hx : g x ≠ 0) (a b c d : E) :
    dz c d (dz a b (fun y => f y / g y)) x =
      dz c d (dz a b f) x / g x -
      (dz a b f x * dz c d g x + dz c d f x * dz a b g x +
        f x * dz c d (dz a b g) x) / (g x)^2 +
      2 * f x * dz a b g x * dz c d g x / (g x)^3 := by
  have hi : ContDiffAt ℝ 2 (fun y => (g y)⁻¹) x := hg.inv hx
  have hd := hg.differentiableAt (by norm_num)
  change dz c d (dz a b (fun y => f y * (g y)⁻¹)) x = _
  rw [dz_mixed_mul_at hf hi, dz_inv_at hd hx, dz_inv_at hd hx,
    dz_mixed_inv_at hg hx]
  field_simp
  ring

theorem complex_ofReal_re_of_star_eq {z : ℂ} (hz : star z = z) : (z.re : ℂ) = z := by
  have hi := congrArg Complex.im hz
  simp only [Complex.star_def, Complex.conj_im] at hi
  have hz0 : z.im = 0 := by linarith
  apply Complex.ext <;> simp [hz0]

end PowerConvexity
