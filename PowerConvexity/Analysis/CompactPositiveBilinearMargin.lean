import PowerConvexity.Analysis.PositiveBilinearTopology

/-! # One bilinear positivity margin on a compact base -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {X : Type*} [TopologicalSpace X]

theorem compact_positive_bilinear_subtraction_margin
    {K : Set X} (hK : IsCompact K)
    (H : X → E →L[ℝ] E →L[ℝ] ℝ) (hH : Continuous H)
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < H x v v) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < (H x-eps • B) v v := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  let F : ℝ × X → E →L[ℝ] E →L[ℝ] ℝ := fun p => H p.2-p.1 • B
  have hF : Continuous F := (hH.comp continuous_snd).sub (continuous_fst.smul continuous_const)
  have hev : ∀ᶠ eps : ℝ in 𝓝 0, ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < F (eps,x) v v :=
    hK.eventually_forall_of_forall_eventually (fun x hx =>
      hF.continuousAt.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds
        (by
          change ∀ v : E, v ≠ 0 → 0 < F (0,x) v v
          simpa only [F,zero_smul,sub_zero] using hpos x hx)))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r/2,by positivity,?_⟩
  have hh : r/2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  exact hball hh

end PowerConvexity
