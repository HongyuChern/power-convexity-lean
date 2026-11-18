import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Stabilization along two normal functionals

A positive quadratic form on the common kernel becomes positive everywhere
after adding a sufficiently large sum of the two squared normal functionals.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_rankTwo_stabilization_positive
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D₁ D₂ : E →L[ℝ] ℝ)
    (hker : ∀ v : E, v ≠ 0 → D₁ v = 0 → D₂ v = 0 → 0 < H v v) :
    ∃ lam > 0, ∀ v : E, v ≠ 0 → 0 < H v v+lam*((D₁ v)^2+(D₂ v)^2) := by
  let O : ℝ → Set E := fun lam => {v | 0 < H v v+lam*((D₁ v)^2+(D₂ v)^2)}
  have hopen (lam : ℝ) : IsOpen (O lam) :=
    isOpen_lt continuous_const ((H.continuous.clm_apply continuous_id).add
      (continuous_const.mul ((D₁.continuous.pow 2).add (D₂.continuous.pow 2))))
  have hcover : sphere (0:E) 1 ⊆ ⋃ lam : ℝ, O lam := by
    intro v hv
    have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    have hv0 : v ≠ 0 := by intro hz; rw [hz,norm_zero] at hvn; norm_num at hvn
    apply mem_iUnion.mpr
    by_cases hD : (D₁ v)^2+(D₂ v)^2 = 0
    · have hD₁ : D₁ v = 0 := by nlinarith [sq_nonneg (D₁ v),sq_nonneg (D₂ v)]
      have hD₂ : D₂ v = 0 := by nlinarith [sq_nonneg (D₁ v),sq_nonneg (D₂ v)]
      exact ⟨0,by simpa only [O,mem_setOf_eq,zero_mul,add_zero] using hker v hv0 hD₁ hD₂⟩
    · refine ⟨(|H v v|+1)/((D₁ v)^2+(D₂ v)^2),?_⟩
      change 0 < H v v+(|H v v|+1)/((D₁ v)^2+(D₂ v)^2)*((D₁ v)^2+(D₂ v)^2)
      rw [div_mul_cancel₀ _ hD]
      linarith [neg_abs_le (H v v)]
  have hdir : Directed (· ⊆ ·) O := by
    intro lam μ
    refine ⟨max lam μ,?_,?_⟩
    · intro v hv
      change 0 < H v v+lam*((D₁ v)^2+(D₂ v)^2) at hv
      change 0 < H v v+max lam μ*((D₁ v)^2+(D₂ v)^2)
      have hh := mul_le_mul_of_nonneg_right (le_max_left lam μ) (add_nonneg (sq_nonneg (D₁ v)) (sq_nonneg (D₂ v)))
      linarith
    · intro v hv
      change 0 < H v v+μ*((D₁ v)^2+(D₂ v)^2) at hv
      change 0 < H v v+max lam μ*((D₁ v)^2+(D₂ v)^2)
      have hh := mul_le_mul_of_nonneg_right (le_max_right lam μ) (add_nonneg (sq_nonneg (D₁ v)) (sq_nonneg (D₂ v)))
      linarith
  obtain ⟨lam,hlam⟩ := (isCompact_sphere (0:E) 1).elim_directed_cover O hopen hcover hdir
  let Λ := max lam 1
  have hΛ : 0 < Λ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hunit (w : E) (hw : ‖w‖ = 1) : 0 < H w w+Λ*((D₁ w)^2+(D₂ w)^2) := by
    have hh := hlam (show w ∈ sphere (0:E) 1 by simpa only [mem_sphere,dist_zero_right] using hw)
    change 0 < H w w+lam*((D₁ w)^2+(D₂ w)^2) at hh
    have hm := mul_le_mul_of_nonneg_right (le_max_left lam 1) (add_nonneg (sq_nonneg (D₁ w)) (sq_nonneg (D₂ w)))
    change lam*((D₁ w)^2+(D₂ w)^2) ≤ Λ*((D₁ w)^2+(D₂ w)^2) at hm
    linarith
  refine ⟨Λ,hΛ,?_⟩
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hn.ne']
  have hh := mul_pos (sq_pos_of_pos hn) (hunit w hw)
  have he : H v v+Λ*((D₁ v)^2+(D₂ v)^2) = ‖v‖^2*(H w w+Λ*((D₁ w)^2+(D₂ w)^2)) := by
    conv_lhs => rw [← hvw]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact hh

end PowerConvexity
