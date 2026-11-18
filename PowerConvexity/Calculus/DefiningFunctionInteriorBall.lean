import PowerConvexity.Calculus.DefiningFunctionSupport

/-! # Interior tangent balls from regular C2 local defining functions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def HasC2LocalDefiningFunction (U : Set E) : Prop :=
  ∀ x ∈ frontier U, ∃ f : E → ℝ, ContDiffAt ℝ 2 f x ∧ f x = 0 ∧
    fderiv ℝ f x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)

def HasSmoothLocalDefiningFunction (U : Set E) : Prop :=
  ∀ x ∈ frontier U, ∃ f : E → ℝ, ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧
    fderiv ℝ f x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)

theorem smoothLocalDefiningFunction_implies_C2 {U : Set E}
    (h : HasSmoothLocalDefiningFunction U) : HasC2LocalDefiningFunction U := by
  intro x hx
  obtain ⟨f,hf,hfx,hD,hdef⟩ := h x hx
  exact ⟨f,(contDiffAt_infty.mp hf) 2,hfx,hD,hdef⟩

theorem exists_interior_ball_of_C2_defining_function
    {U : Set E} {x N : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hN : N ≠ 0)
    (hD : ∀ v : E, fderiv ℝ f x v = inner ℝ N v)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ r > 0, ball (x-r • N) (r*‖N‖) ⊆ U := by
  obtain ⟨C,hC,δ,hδ,hTaylor⟩ := exists_local_quadratic_remainder_bound hf
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp hdef
  let η₀ := min δ η
  have hη₀ : 0 < η₀ := lt_min hδ hη
  let r := min (1/(2*(C+1))) (η₀/(2*(‖N‖+1)))
  have hr : 0 < r := lt_min (by positivity) (div_pos hη₀ (by positivity))
  have hrC : 2*r*C ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp (show r ≤ 1/(2*(C+1)) from min_le_left _ _)
    change r*(2*(C+1)) ≤ 1 at hh
    nlinarith
  have hrN : 2*r*‖N‖ ≤ η₀ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(‖N‖+1))).mp (show r ≤ η₀/(2*(‖N‖+1)) from min_le_right _ _)
    change r*(2*(‖N‖+1)) ≤ η₀ at hh
    nlinarith
  refine ⟨r,hr,?_⟩
  intro z hz
  let c := x-r • N
  let R := r*‖N‖
  have hR : 0 < R := mul_pos hr (norm_pos_iff.mpr hN)
  have hzR : ‖z-c‖ < R := by simpa only [mem_ball,dist_eq_norm] using hz
  have hcx : ‖c-x‖ = R := by
    rw [show c-x = -r • N by dsimp [c]; module,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hr]
  have hzx : ‖z-x‖ < η₀ := by
    have hh : ‖z-x‖ ≤ ‖z-c‖+‖c-x‖ := by
      rw [show z-x = (z-c)+(c-x) by abel]
      exact norm_add_le _ _
    rw [hcx] at hh
    dsimp [R] at hzR hh
    linarith
  have hηz : z ∈ ball x η := by
    rw [mem_ball,dist_eq_norm]
    exact hzx.trans_le (min_le_right _ _)
  apply (hηball hηz).mpr
  have ht := (abs_le.mp (hTaylor z (hzx.trans_le (min_le_left _ _)))).2
  rw [hfx,sub_zero,hD] at ht
  have hsq : ‖z-c‖^2 < R^2 := by nlinarith [norm_nonneg (z-c)]
  rw [show z-c = (z-x)+r • N by dsimp [c]; module,norm_add_sq_real,
    real_inner_smul_right,real_inner_comm N (z-x),norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hsq
  have hb : ‖z-x‖^2+2*r*inner ℝ N (z-x) < 0 := by
    dsimp [R] at hsq
    nlinarith
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*r by positivity)
  have hrest := mul_le_mul_of_nonneg_right hrC (sq_nonneg ‖z-x‖)
  nlinarith

end PowerConvexity
