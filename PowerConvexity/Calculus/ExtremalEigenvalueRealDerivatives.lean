import PowerConvexity.Calculus.ExtremalEigenvalueDerivatives

/-! # Appendix B in literal real Frechet directional derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_add_self_zero (a : E) (f : E → ℂ) :
    dz (a+a) 0 f = fun x => fderiv ℝ f x a := by
  funext x
  simp only [dz,rd,map_add,map_zero,mul_zero,sub_zero]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem SimpleRealEigenvalueJet.real_derivatives
    {K : E → Matrix ι ι ℂ} {f : E → ℝ} {x : E} {i : ι} {d : ι → ℝ}
    (h : SimpleRealEigenvalueJet K f x i d) (a c : E) :
    fderiv ℝ (fun y => (f y:ℂ)) x a = fderiv ℝ (fun y => K y i i) x a ∧
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z:ℂ)) y a) x c =
      fderiv ℝ (fun y => fderiv ℝ (fun z => K z i i) y a) x c +
      ∑ j : {j : ι // j ≠ i},
        (fderiv ℝ (fun y => K y i j) x a * fderiv ℝ (fun y => K y j i) x c +
          fderiv ℝ (fun y => K y i j) x c * fderiv ℝ (fun y => K y j i) x a) /
          ((d i:ℂ)-(d j:ℂ)) := by
  simpa only [dz_add_self_zero] using h.2.2 (a+a) 0 (c+c) 0

end PowerConvexity
