import PowerConvexity.Calculus.QuadraticBallPotential

/-! # A strict psh quadratic in a prescribed negative band on a compact set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_small_negative_strictPsh_quadratic_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {K : Set E} (hK : IsCompact K) {d : ℝ} (hd : 0 < d) :
    ∃ q : E → ℝ, ContDiff ℝ 4 q ∧
      (∀ x, (complexHessian a b q x).PosDef) ∧
      ∀ x ∈ K, -d/2 ≤ q x ∧ q x ≤ -d/4 := by
  obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
  let A := max L 0
  have hA : 0 ≤ A := le_max_right _ _
  let c := d/(4*(A^2+1))
  have hc : 0 < c := div_pos hd (by positivity)
  have hceq : c*(A^2+1) = d/4 := by
    dsimp only [c]
    field_simp
  let q : E → ℝ := fun x => c*‖x‖^2-d/2
  have hq : ContDiff ℝ 4 q := (contDiff_const.mul (contDiff_norm_sq ℝ)).sub contDiff_const
  refine ⟨q,hq,?_,?_⟩
  · intro x
    have he : complexHessian a b q x = (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      change complexHessian a b (fun y => c*‖y‖^2-d/2) x = _
      simp only [sub_eq_add_neg]
      rw [complexHessian_add_const,complexHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
        norm_square_complexHessian a b hab]
    rw [he]
    exact Matrix.PosDef.one.smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  · intro x hx
    have hxA : ‖x‖ ≤ A := (hL x hx).trans (le_max_left _ _)
    have hs : ‖x‖^2 ≤ A^2 := (sq_le_sq₀ (norm_nonneg x) hA).mpr hxA
    have hlow := mul_nonneg hc.le (sq_nonneg ‖x‖)
    have hupp := mul_le_mul_of_nonneg_left hs hc.le
    dsimp only [q]
    constructor <;> nlinarith

end PowerConvexity
