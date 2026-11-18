import PowerConvexity.Calculus.ModifiedSchur

/-! # Strict psh of the power transform is exactly positivity of modifiedA -/
set_option autoImplicit false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem power_mixed_posDef_iff_modifiedA {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) :
    (complexHessian a b (powerTransform u) x).PosDef ↔ (modifiedA a b u x).PosDef := by
  rw [power_mixed_matrix hu hx]
  have hs : 0 < (sqrtSlope (u x):ℂ) := by exact_mod_cast sqrtSlope_pos hx
  have hn : (sqrtSlope (u x):ℂ) ≠ 0 := ne_of_gt hs
  constructor
  · intro h
    have hi : 0 < ((sqrtSlope (u x))⁻¹:ℝ) := inv_pos.mpr (sqrtSlope_pos hx)
    have hic : 0 < (((sqrtSlope (u x))⁻¹:ℝ):ℂ) := by exact_mod_cast hi
    have hh := h.smul hic
    simpa only [Complex.ofReal_inv,smul_smul,inv_mul_cancel₀ hn,one_smul] using hh
  · intro h
    exact h.smul hs

end PowerConvexity
