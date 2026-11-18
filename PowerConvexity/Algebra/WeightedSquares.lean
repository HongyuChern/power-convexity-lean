import PowerConvexity.Algebra.DimensionTwo
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Exact weighted squares, preserving the inverse-Hessian index order -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weightedSquare (G : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑ p, ∑ q, G q p*v p*star (v q)

theorem weightedSquare_eq_dotProduct (G : Matrix ι ι ℂ) (v : ι → ℂ) :
    weightedSquare G v = star v ⬝ᵥ (G *ᵥ v) := by
  simp only [weightedSquare,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem weightedSquare_nonneg {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (v : ι → ℂ) :
    0 ≤ weightedSquare G v := by
  rw [weightedSquare_eq_dotProduct]
  exact hG.dotProduct_mulVec_nonneg v

theorem weightedSquare_re_nonneg {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (v : ι → ℂ) :
    0 ≤ (weightedSquare G v).re := (Complex.nonneg_iff.mp (weightedSquare_nonneg hG v)).1

/-- The square completion in Steps 5--6 is valid for the actual inverse
weight G, with no unit-density or diagonal-weight hypothesis. -/
theorem weightedSquare_completion (G : Matrix ι ι ℂ) (X D : ι → ℂ)
    (b : ℝ) (hμ : (1-(b:ℂ)^2) ≠ 0) :
    weightedSquare G D + weightedSquare G (fun p => X p-(b:ℂ)*D p)/(1-(b:ℂ)^2) =
      weightedSquare G X + weightedSquare G (fun p => (b:ℂ)*X p-D p)/(1-(b:ℂ)^2) := by
  apply mul_right_cancel₀ hμ
  simp only [add_mul,div_mul_cancel₀ _ hμ]
  unfold weightedSquare
  simp only [Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_sub_distrib,
    map_sub,map_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end PowerConvexity
