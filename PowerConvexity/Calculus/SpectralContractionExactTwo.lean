import PowerConvexity.Calculus.ModifiedContactSpectrumTwo
import PowerConvexity.Calculus.NormComplement
import PowerConvexity.Algebra.SpectralGradientBoundsTwo
import PowerConvexity.Algebra.WeightedSquares

/-! # Exact actual simple-root contraction before discarding any remainder -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def modifiedPencilFirstVectorTwo (a b : Fin 2 → E) (u : E → ℝ)
    (x : E) (i j : Fin 2) : Fin 2 → ℂ := fun p =>
  dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x-
    (modifiedSigmaTwo a b u x:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y i j) x

theorem modifiedA_dzbar_eq_star_swap {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin 2 → E) (i j q : Fin 2) :
    dz (a q) (-b q) (fun y => modifiedA a b u y i j) x =
      star (dz (a q) (b q) (fun y => modifiedA a b u y j i) x) := by
  have he := congrArg star (dz_modifiedA_star_swap hu a b i j q)
  rw [dz_star_reverse,star_star] at he
  exact he

theorem dzbar_ofReal_eq_star (a b : E) (f : E → ℝ) (x : E) :
    dz a (-b) (fun y => (f y:ℂ)) x = star (dz a b (fun y => (f y:ℂ)) x) := by
  simpa only [Complex.star_def,Complex.conj_ofReal] using
    dz_star_flip a b (fun y => (f y:ℂ)) x

theorem modifiedSigmaTwo_contraction_normalized_exact {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (horder : d 1 < d 0) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) =
    matrixL a b u (modifiedSchur a b u) x 0 0-
      (modifiedSigmaTwo a b u x:ℂ)*matrixL a b u (modifiedA a b u) x 0 0-
      spectralGradientCrossTwo (complexHessian a b u x)⁻¹
        (fun p => dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ)) x)
        (fun p => dz (a p) (b p) (fun y => modifiedA a b u y 0 0) x)-
      weightedSquare (complexHessian a b u x)⁻¹ (modifiedPencilFirstVectorTwo a b u x 0 1)/
        ((d 0^2-d 1^2:ℝ):ℂ)-
      weightedSquare (complexHessian a b u x)⁻¹ (modifiedPencilFirstVectorTwo a b u x 1 0)/
        ((d 0^2-d 1^2:ℝ):ℂ) := by
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hm (p q : Fin 2) := modifiedSigmaTwo_mixed_normalized_exact hU hu a b hneg hA hx d hI hD
    hd0 hd1 horder (a p) (b p) (a q) (-b q)
  simp_rw [modifiedSchur_dzbar_eq_star_swap hU hu a b hneg hA hx,
    modifiedA_dzbar_eq_star_swap hu3 a b,dzbar_ofReal_eq_star] at hm
  simp_rw [hm]
  simp only [matrixL_entry,spectralGradientCrossTwo,weightedSquare,modifiedPencilFirstVectorTwo,
    Fin.sum_univ_two,star_sub,star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

end PowerConvexity
