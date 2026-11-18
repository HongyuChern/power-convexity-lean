import CHS.CoreImports

/-!
# Exact algebra behind the Appendix C scalar inequality

The input z is the holomorphic derivative of q=beta/alpha.  The formulas
below are inserted into the actual calculus in AppendixCRatio.  This ring
identity replaces informal error suppression by an exact equality.
-/

set_option autoImplicit false

namespace PowerConvexity

theorem scalar_sigma_algebra (h α : ℝ) (q g z : ℂ) :
    let R := q * star q
    let σ := 1 - R
    let qb := (h : ℂ) * ((1 + σ) * g - q * star g)
    let s := -z * star q - q * star qb
    let T := (h : ℂ) * α * σ * q + (h : ℂ) * s * g +
      (h : ℂ)^2 * (1 + σ) * g^2 - (h : ℂ)^2 * q * g * star g -
      (h : ℂ) * z * star g
    let t := -T * star q - q * star T - z * star z - qb * star qb
    R * t = -s * star s - 2 * (h : ℂ) * (s * g * star q + star s * star g * q) -
      2 * (h : ℂ) * α * σ * R^2 -
      2 * (h : ℂ)^2 * σ * (3 + σ) * R * g * star g := by
  dsimp only
  simp only [star_add, star_sub, star_mul, star_neg, star_pow, star_one, star_ofNat,
    star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

end PowerConvexity
