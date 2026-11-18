import PowerConvexity.Calculus.ScalarSecondCalculus

/-!
# Exact simple-eigenvalue derivatives in dimension two

These are derivatives of an actual local characteristic-root function.
The characteristic equation holds on a neighbourhood, not just at the
calculation point.  No eigenvector differentiability is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_equation_dz_at {f g c d : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (he : (fun y => f y * g y - c y * d y) =ᶠ[𝓝 x] fun _ => (0 : ℂ))
    (hfx : f x = 0) (hcx : c x = 0) (hdx : d x = 0) (hgx : g x ≠ 0)
    (a b : E) : dz a b f x = 0 := by
  have hz := dz_of_eventually_const he a b
  have hs := dz_sub_at (hf.mul hg) (hc.mul hd) a b
  have h1 := dz_mul_at hf hg a b
  have h2 := dz_mul_at hc hd a b
  simp only [Pi.sub_def, Pi.sub_apply, Pi.mul_def, Pi.mul_apply] at hs h1 h2
  rw [hs, h1, h2, hfx, hcx, hdx] at hz
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_right hgx

theorem product_equation_mixed_at {f g c d : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (he : (fun y => f y * g y - c y * d y) =ᶠ[𝓝 x] fun _ => (0 : ℂ))
    (hfx : f x = 0) (hcx : c x = 0) (hdx : d x = 0) (hgx : g x ≠ 0)
    (a b v w : E) :
    dz v w (dz a b f) x =
      (dz a b c x * dz v w d x + dz v w c x * dz a b d x) / g x := by
  have hf1 := hf.differentiableAt (by norm_num)
  have hg1 := hg.differentiableAt (by norm_num)
  have hc1 := hc.differentiableAt (by norm_num)
  have hd1 := hd.differentiableAt (by norm_num)
  have hfa := product_equation_dz_at hf1 hg1 hc1 hd1 he hfx hcx hdx hgx a b
  have hfv := product_equation_dz_at hf1 hg1 hc1 hd1 he hfx hcx hdx hgx v w
  have hz := dz_dz_of_eventually_const he v w a b
  have hs := dz_mixed_sub_at (hf.mul hg) (hc.mul hd) a b v w
  rw [hs, dz_mixed_mul_at hf hg, dz_mixed_mul_at hc hd,
    hfx, hcx, hdx, hfa, hfv] at hz
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hz
  apply (eq_div_iff hgx).mpr
  linear_combination hz

/-- Appendix B `B2-1`, for a genuine root near a diagonal calculation point. -/
theorem simple_eigenvalueTwo_dz {K : E → Matrix (Fin 2) (Fin 2) ℂ}
    {ell : E → ℂ} {x : E} (hK : MatrixDifferentiableAt K x)
    (hell : DifferentiableAt ℝ ell x)
    (hroot : (fun y => (K y 0 0 - ell y) * (K y 1 1 - ell y) -
      K y 0 1 * K y 1 0) =ᶠ[𝓝 x] fun _ => (0 : ℂ))
    (h00 : K x 0 0 = ell x) (h01 : K x 0 1 = 0) (h10 : K x 1 0 = 0)
    (hgap : K x 1 1 - ell x ≠ 0) (a b : E) :
    dz a b ell x = dz a b (fun y => K y 0 0) x := by
  have h := product_equation_dz_at ((hK 0 0).sub hell) ((hK 1 1).sub hell)
    (hK 0 1) (hK 1 0) hroot (by simp [h00]) h01 h10 hgap a b
  have hs := dz_sub_at (hK 0 0) hell a b
  simp only [Pi.sub_def, Pi.sub_apply] at h hs
  rw [hs] at h
  exact (sub_eq_zero.mp h).symm

/-- Appendix B `B2-2` / `3.2-1`, with the two cross-products and the actual gap. -/
theorem simple_eigenvalueTwo_mixed {K : E → Matrix (Fin 2) (Fin 2) ℂ}
    {ell : E → ℂ} {x : E} (hK : ∀ i j, ContDiffAt ℝ 2 (fun y => K y i j) x)
    (hell : ContDiffAt ℝ 2 ell x)
    (hroot : (fun y => (K y 0 0 - ell y) * (K y 1 1 - ell y) -
      K y 0 1 * K y 1 0) =ᶠ[𝓝 x] fun _ => (0 : ℂ))
    (h00 : K x 0 0 = ell x) (h01 : K x 0 1 = 0) (h10 : K x 1 0 = 0)
    (hgap : K x 1 1 - ell x ≠ 0) (a b v w : E) :
    dz v w (dz a b ell) x = dz v w (dz a b (fun y => K y 0 0)) x -
      (dz a b (fun y => K y 0 1) x * dz v w (fun y => K y 1 0) x +
        dz v w (fun y => K y 0 1) x * dz a b (fun y => K y 1 0) x) /
      (K x 1 1 - ell x) := by
  have h := product_equation_mixed_at ((hK 0 0).sub hell) ((hK 1 1).sub hell)
    (hK 0 1) (hK 1 0) hroot (by simp [h00]) h01 h10 hgap a b v w
  have hs := dz_mixed_sub_at (hK 0 0) hell a b v w
  rw [hs] at h
  linear_combination -h

end PowerConvexity
