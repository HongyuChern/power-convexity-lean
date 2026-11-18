import PowerConvexity.Analysis.CompactSmallParameter
import PowerConvexity.Analysis.RankOneBoundaryPositivity

/-! # Openness of positivity of actual continuous bilinear forms -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem bilinear_positive_of_unit_sphere
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hunit : ∀ w : E, ‖w‖ = 1 → 0 < H w w) :
    ∀ v : E, v ≠ 0 → 0 < H v v := by
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hn.ne']
  have he : H v v = ‖v‖^2*(H w w) := by
    conv_lhs => rw [← hvw]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact mul_pos (sq_pos_of_pos hn) (hunit w hw)

theorem isOpen_positive_bilinear_forms :
    IsOpen {H : E →L[ℝ] E →L[ℝ] ℝ | ∀ v : E, v ≠ 0 → 0 < H v v} := by
  rw [isOpen_iff_mem_nhds]
  intro H hH
  have hc : Continuous (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × E => z.1 z.2 z.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hh : ∀ᶠ Q in 𝓝 H, ∀ v ∈ sphere (0:E) 1, 0 < Q v v :=
    (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually (fun v hv => by
      have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
      have hv0 : v ≠ 0 := by intro hz; rw [hz,norm_zero] at hvn; norm_num at hvn
      exact hc.continuousAt.tendsto.eventually (lt_mem_nhds (hH v hv0)))
  filter_upwards [hh] with Q hQ
  exact bilinear_positive_of_unit_sphere Q (fun v hv => hQ v (by
    simpa only [mem_sphere,dist_zero_right] using hv))

theorem positive_bilinear_eventually_within {X : Type*} [TopologicalSpace X]
    {S : Set X} {x : X} {H : X → (E →L[ℝ] E →L[ℝ] ℝ)}
    (hc : ContinuousWithinAt H S x) (hp : ∀ v : E, v ≠ 0 → 0 < H x v v) :
    ∀ᶠ y in 𝓝[S] x, ∀ v : E, v ≠ 0 → 0 < H y v v :=
  hc.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hp)

end PowerConvexity
