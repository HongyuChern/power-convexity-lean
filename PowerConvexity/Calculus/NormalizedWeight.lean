import PowerConvexity.Algebra.RankOneInverse
import PowerConvexity.Calculus.ModifiedDerivatives
import PowerConvexity.Calculus.LocalDimensionTwo

/-! # The actual inverse complex Hessian in the frame `𝒜 = I`

This removes the independent weight-representation hypothesis from C01's
local dimension-two sign theorem.  The normalization itself is still stated
explicitly; coordinate covariance does not assert existence of a Takagi frame.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem originalHessian_eq_normalized_rankOne {u : E → ℝ} {x : E}
    (a b : ι → E) (hI : modifiedA a b u x = 1) :
    complexHessian a b u x =
      1 - (powerWeight (u x) : ℂ) •
        Matrix.vecMulVec (complexGradient a b u x) (star (complexGradient a b u x)) := by
  rw [modifiedA_eq_rankOne] at hI
  exact eq_sub_of_add_eq hI

theorem normalized_gradient_gap {u : E → ℝ} {x : E}
    (a b : ι → E) (hI : modifiedA a b u x = 1)
    (hA : (complexHessian a b u x).PosDef) :
    0 < 1 - powerWeight (u x) * vectorNormSq (complexGradient a b u x) := by
  apply rankOne_denominator_pos
  rwa [← originalHessian_eq_normalized_rankOne a b hI]

theorem originalHessian_inverse_eq_normalized_rankOne {u : E → ℝ} {x : E}
    (a b : ι → E) (hx : u x < 0) (hI : modifiedA a b u x = 1)
    (hA : (complexHessian a b u x).PosDef) :
    (complexHessian a b u x)⁻¹ =
      1 + Matrix.vecMulVec
        (normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x))
        (star (normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x))) := by
  rw [originalHessian_eq_normalized_rankOne a b hI] at hA ⊢
  apply inverse_one_sub_outer_eq_rankOne _ _ _ hA
  unfold powerWeight
  exact (one_div_pos.mpr (mul_pos (by norm_num) (neg_pos.mpr hx))).le

/-- TeX `8.1`, with both `W` and the rank-one inverse derived from the same u. -/
theorem local_dimensionTwo_sign_normalized {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin 2 → E) (hx : u x < 0)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (hI : modifiedA a b u x = 1) (hA : (complexHessian a b u x).PosDef)
    (k : Fin 2) :
    Complex.normSq (Matrix.trace (skewThirdHessian a b u k x)) ≤
      ∑ p, ∑ q, Complex.normSq (skewThirdHessian a b u k x p q) := by
  apply local_dimensionTwo_sign hu a b hdet k
    (normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x))
  exact originalHessian_inverse_eq_normalized_rankOne a b hx hI hA

end PowerConvexity
