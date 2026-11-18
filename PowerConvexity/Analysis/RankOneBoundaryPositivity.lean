import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Rank-one stabilization of a boundary Hessian

Positivity on the kernel of a nonzero normal is a genuine extra geometric
input. It is kept explicit and is not inferred from strict convexity of sets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_rankOne_stabilization_positive
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] ℝ)
    (hker : ∀ v : E, v ≠ 0 → D v = 0 → 0 < H v v) :
    ∃ lam > 0, ∀ v : E, v ≠ 0 → 0 < H v v+lam*(D v)^2 := by
  let O : ℝ → Set E := fun lam => {v | 0 < H v v+lam*(D v)^2}
  have hopen (lam : ℝ) : IsOpen (O lam) :=
    isOpen_lt continuous_const ((H.continuous.clm_apply continuous_id).add
      (continuous_const.mul (D.continuous.pow 2)))
  have hcover : sphere (0:E) 1 ⊆ ⋃ lam : ℝ, O lam := by
    intro v hv
    have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    have hv0 : v ≠ 0 := by intro hz; rw [hz,norm_zero] at hvn; norm_num at hvn
    apply mem_iUnion.mpr
    by_cases hD : D v = 0
    · exact ⟨0,by simpa only [O,mem_setOf_eq,zero_mul,add_zero] using hker v hv0 hD⟩
    · refine ⟨(|H v v|+1)/(D v)^2,?_⟩
      change 0 < H v v+(|H v v|+1)/(D v)^2*(D v)^2
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
      linarith [neg_abs_le (H v v)]
  have hdir : Directed (· ⊆ ·) O := by
    intro lam μ
    refine ⟨max lam μ,?_,?_⟩
    · intro v hv
      change 0 < H v v+lam*(D v)^2 at hv
      change 0 < H v v+max lam μ*(D v)^2
      have hh := mul_le_mul_of_nonneg_right (le_max_left lam μ) (sq_nonneg (D v))
      linarith
    · intro v hv
      change 0 < H v v+μ*(D v)^2 at hv
      change 0 < H v v+max lam μ*(D v)^2
      have hh := mul_le_mul_of_nonneg_right (le_max_right lam μ) (sq_nonneg (D v))
      linarith
  obtain ⟨lam,hlam⟩ := (isCompact_sphere (0:E) 1).elim_directed_cover O hopen hcover hdir
  let Λ := max lam 1
  have hΛ : 0 < Λ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hunit (w : E) (hw : ‖w‖ = 1) : 0 < H w w+Λ*(D w)^2 := by
    have hh := hlam (show w ∈ sphere (0:E) 1 by simpa only [mem_sphere,dist_zero_right] using hw)
    change 0 < H w w+lam*(D w)^2 at hh
    have hm := mul_le_mul_of_nonneg_right (le_max_left lam 1) (sq_nonneg (D w))
    change lam*(D w)^2 ≤ Λ*(D w)^2 at hm
    linarith
  refine ⟨Λ,hΛ,?_⟩
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hn.ne']
  have hh := mul_pos (sq_pos_of_pos hn) (hunit w hw)
  have he : H v v+Λ*(D v)^2 = ‖v‖^2*(H w w+Λ*(D w)^2) := by
    conv_lhs => rw [← hvw]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact hh

end PowerConvexity
