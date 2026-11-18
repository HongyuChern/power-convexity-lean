import PowerConvexity.Calculus.AppendixCMixedRatio

/-!
# Exact scalar sigma equation and the gradient term in Appendix C

All derivatives refer to the actual potential.  The constant mixed Hessian
may be any local constant rho, which includes positive constant density after
a complex linear coordinate change.  No normalized value alpha=1 or beta=1
is substituted in a differentiated expression.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarSigma_equation_complex {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x ≠ 0) :
    let h : ℂ := powerWeight (u x)
    let α := scalarAlpha a b u x
    let g := dz a b (fun y => (u y : ℂ)) x
    let q := scalarRatio a b u x
    let σ : ℂ := scalarSigma a b u x
    let R := q * star q
    let s := dz a b (fun y => (scalarSigma a b u y : ℂ)) x
    R * dz a (-b) (dz a b (fun y => (scalarSigma a b u y : ℂ))) x =
      -s * star s - 2 * h * (s * g * star q + star s * star g * q) -
      2 * h * α * σ * R^2 - 2 * h^2 * σ * (3 + σ) * R * g * star g := by
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hσ := scalarSigma_cast_eq_ratio h2 a b
  have hqb := scalarRatio_dzbar hu hx a b hρ hα
  have hs := scalarSigma_dz hu hx a b hα
  have hT := scalarRatio_dzbar_dz hu hx a b hρ hα
  have ht := scalarSigma_dzbar_dz hu hx a b hα
  have hreal := complex_ofReal_re_of_star_eq (scalarAlpha_star h2 a b)
  have halg := scalar_sigma_algebra (powerWeight (u x)) (scalarAlpha a b u x).re
    (scalarRatio a b u x) (dz a b (fun y => (u y : ℂ)) x)
    (dz a b (scalarRatio a b u) x)
  dsimp only at halg hT ht ⊢
  rw [← hσ, ← hqb, ← hs, hreal, ← hT, ← ht] at halg
  exact halg

theorem complex_mul_star_normSq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem scalarSigma_equation_real {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x ≠ 0) :
    let h := powerWeight (u x)
    let α := (scalarAlpha a b u x).re
    let g := dz a b (fun y => (u y : ℂ)) x
    let q := scalarRatio a b u x
    let σ := scalarSigma a b u x
    let R := Complex.normSq q
    let s := dz a b (fun y => (scalarSigma a b u y : ℂ)) x
    R * (dz a (-b) (dz a b (fun y => (scalarSigma a b u y : ℂ))) x).re =
      -Complex.normSq s - 4 * h * (s * g * star q).re -
      2 * h * α * σ * R^2 - 2 * h^2 * σ * (3 + σ) * R * Complex.normSq g := by
  have hc := scalarSigma_equation_complex hu hx a b hρ hα
  have hreal := complex_ofReal_re_of_star_eq
    (scalarAlpha_star (hu.of_le (by norm_num)) a b)
  dsimp only at hc ⊢
  rw [← hreal] at hc
  simp only [neg_mul, complex_mul_star_normSq] at hc
  have he := congrArg Complex.re hc
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.neg_re, pow_two, Complex.normSq_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at he ⊢
  norm_num at he ⊢
  linear_combination he

end PowerConvexity
