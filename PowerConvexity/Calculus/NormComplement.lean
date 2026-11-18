import PowerConvexity.Calculus.ScalarQuotientCalculus

/-! # Actual derivatives of the norm complement 1 - |q|^2 -/

set_option autoImplicit false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_dz_congr_nhds {f g : E → ℂ} {x : E}
    (hfg : f =ᶠ[𝓝 x] g) (a b c d : E) :
    dz c d (dz a b f) x = dz c d (dz a b g) x := by
  apply dz_congr_nhds
  exact hfg.eventuallyEq_nhds.mono fun y hy => dz_congr_nhds hy a b

theorem dz_star_reverse (a b : E) (f : E → ℂ) (x : E) :
    dz a b (fun y => star (f y)) x = star (dz a (-b) f x) := by
  simpa only [neg_neg] using dz_star_flip a (-b) f x

theorem dz_mixed_star_at {q : E → ℂ} {x : E}
    (hq : ContDiffAt ℝ 2 q x) (a b : E) :
    dz a (-b) (dz a b (fun y => star (q y))) x =
      star (dz a (-b) (dz a b q) x) := by
  have he : dz a b (fun y => star (q y)) =
      fun y => star (dz a (-b) q y) := funext fun y => dz_star_reverse a b q y
  rw [he, dz_star_flip, dz_comm_at hq]

theorem normComplement_cast (q : E → ℂ) (x : E) :
    ((1 - Complex.normSq (q x) : ℝ) : ℂ) = 1 - q x * star (q x) := by
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]
  ring

theorem normComplement_dz {q : E → ℂ} {x : E}
    (hq : DifferentiableAt ℝ q x) (a b : E) :
    dz a b (fun y => ((1 - Complex.normSq (q y) : ℝ) : ℂ)) x =
      -dz a b q x * star (q x) - q x * star (dz a (-b) q x) := by
  have he := funext (normComplement_cast q)
  have hs := dz_sub_at (differentiableAt_const (1 : ℂ)) (hq.mul hq.star) a b
  simp only [Pi.mul_def] at hs
  rw [he, hs, dz_const,
    dz_mul_at hq hq.star, dz_star_reverse]
  ring

theorem normComplement_dzbar_dz {q : E → ℂ} {x : E}
    (hq : ContDiffAt ℝ 2 q x) (a b : E) :
    dz a (-b) (dz a b (fun y => ((1 - Complex.normSq (q y) : ℝ) : ℂ))) x =
      -dz a (-b) (dz a b q) x * star (q x) -
      q x * star (dz a (-b) (dz a b q) x) -
      dz a b q x * star (dz a b q x) -
      dz a (-b) q x * star (dz a (-b) q x) := by
  have hc : ContDiffAt ℝ 2 (fun y => star (q y)) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x hq
  have he := funext (normComplement_cast q)
  rw [he, dz_mixed_sub_at contDiffAt_const (hq.mul hc),
    dz_dz_of_eventually_const (Filter.EventuallyEq.rfl),
    dz_mixed_mul_at hq hc, dz_star_flip, dz_star_reverse, dz_mixed_star_at hq]
  ring

end PowerConvexity
