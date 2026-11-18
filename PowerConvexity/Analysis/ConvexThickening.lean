import PowerConvexity.Calculus.HomotheticDirichletTwo

/-! # A convex set containing a ball absorbs metric thickenings by homothety -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_add_small_vector_mem_dilation {U : Set E} (hU : Convex ℝ U)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hball : closedBall (0:E) ρ ⊆ U)
    {x h : E} (hx : x ∈ U) (hh : ‖h‖ ≤ δ) :
    (1+δ/ρ)⁻¹ • (x+h) ∈ U := by
  by_cases hδ0 : δ = 0
  · have hh0 : h = 0 := norm_eq_zero.mp (le_antisymm (hδ0 ▸ hh) (norm_nonneg _))
    simpa [hδ0,hh0] using hx
  have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  let s := 1+δ/ρ
  have hs : 0 < s := by dsimp only [s]; positivity
  have hw : (ρ/δ) • h ∈ U := by
    apply hball
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hρ hδp)]
    have hb := mul_le_mul_of_nonneg_left hh (div_nonneg hρ.le hδ)
    calc
      (ρ/δ)*‖h‖ ≤ (ρ/δ)*δ := hb
      _ = ρ := div_mul_cancel₀ ρ hδ0
  have hsum : s⁻¹+(δ/ρ)/s = 1 := by
    dsimp only [s]
    field_simp [hρ.ne',hs.ne']
    <;> ring
  have hc := hU hx hw (inv_nonneg.mpr hs.le) (div_nonneg (div_nonneg hδ hρ.le) hs.le) hsum
  have he : s⁻¹ • x+((δ/ρ)/s) • ((ρ/δ) • h) = s⁻¹ • (x+h) := by
    rw [smul_smul,smul_add]
    have hh : ((δ/ρ)/s)*(ρ/δ) = s⁻¹ := by field_simp [hρ.ne',hδ0,hs.ne']
    rw [hh]
  rw [he] at hc
  exact hc

end PowerConvexity
