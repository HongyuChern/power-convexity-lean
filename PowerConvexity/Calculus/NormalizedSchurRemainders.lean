import PowerConvexity.Calculus.ModifiedPencilTwo
import PowerConvexity.Calculus.NormalizedContactColumn

/-! # Exact sigma and Dsigma remainders before taking zero contact -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalizedThirdRemainder (a b : ι → E) (u : E → ℝ)
    (k : ι) (x : E) (p s : ι) : ℂ :=
  dz (a p) (b p) (fun y => star (pureHessian a b u y k s)) x+
  (powerWeight (u x):ℂ)*star (complexGradient a b u x k)*(1 : Matrix ι ι ℂ) p s

theorem modifiedSchur_column_normalized_remainder {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ))) (k s p : ι) :
    let X := skewThirdHessian a b u k x p s+
      (powerWeight (u x):ℂ)*(complexGradient a b u x k-star (complexGradient a b u x k))*
        (1 : Matrix ι ι ℂ) p s
    let H := (d s:ℂ)*X-modifiedCompensatedHessian a b u p x k s
    dz (a p) (b p) (fun y => modifiedSchur a b u y s k) x =
      H+(1-(d k:ℂ))*(-H+(d s:ℂ)*(d k:ℂ)*normalizedThirdRemainder a b u k x p s+
        (1+(d k:ℂ))*(dz (a p) (b p) (fun y => modifiedA a b u y s k) x-
          (d s:ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y k s)) x)) := by
  dsimp only
  have hr := modifiedSchur_dz_normalized_remainder hu hx a b hA d hI hD k s p
  rw [modifiedSchur_dz_normalized_direct hu hx a b hA d hI hD k s p] at hr
  rw [modifiedSchur_dz_normalized_direct hu hx a b hA d hI hD s k p,
    modifiedCompensated_transpose_difference (hu.of_le (by norm_num)) a b d hI hD k s p,
    dz_modifiedB_star_swap (hu.of_le (by norm_num)) a b s k p]
  unfold normalizedThirdRemainder
  linear_combination (d s:ℂ)*(d k:ℂ)*hr

theorem modifiedCompensated_first_column_defect {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0) (p : Fin 2) :
    modifiedCompensatedHessian a b u p x 0 0-
      (skewThirdHessian a b u 0 x p 0+
        (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))*
          (1 : Matrix (Fin 2) (Fin 2) ℂ) p 0) =
      (1-(d 0:ℂ))*(modifiedCompensatedHessian a b u p x 0 0+normalizedThirdRemainder a b u 0 x p 0)-
      dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ)) x-
      (modifiedSigmaTwo a b u x:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y 0 0) x := by
  have hr := modifiedSchur_dz_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) d hI hD 0 0 p
  have hs := modifiedSigmaTwo_dz_normalized_exact hU hu a b hneg hA hx d hI hD hd0 hd1 ho (a p) (b p)
  unfold normalizedThirdRemainder
  linear_combination hr+hs

end PowerConvexity
