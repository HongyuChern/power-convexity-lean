import PowerConvexity.Calculus.DerivativeOscillationStability
import PowerConvexity.Analysis.CompactSmallParameter

/-! # Joint derivative continuity from local values and equicontinuity

This is a closed analytic criterion. Uniform derivative oscillation remains an
explicit estimate to discharge when this is applied to second jets of PDE solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {T E F : Type*} [TopologicalSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_family_norm_close_of_local_joint_continuity
    {G : T → E → F} {t0 : T} {K : Set E} (hK : IsCompact K)
    (hG : ∀ y ∈ K, ContinuousAt (fun p : T × E => G p.1 p.2) (t0,y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t0, ∀ y ∈ K, ‖G t y-G t0 y‖ < ε := by
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hb : ContinuousAt (G t0) y := (hG y hy).comp (continuousAt_const.prodMk continuousAt_id)
  have hd := (hG y hy).sub (hb.comp continuousAt_snd)
  have hn := ContinuousAt.norm (E := F) hd
  have hz : ‖G t0 y-G t0 y‖ < ε := by simpa using hε
  exact hn.tendsto.eventually (gt_mem_nhds hz)

theorem family_fderiv_continuousAt_of_uniform_oscillation [ProperSpace E]
    {G : T → E → F} {t0 : T} {x0 : E} {R : ℝ} (hR : 0 < R)
    (hG : ∀ y ∈ closedBall x0 R, ContinuousAt (fun p : T × E => G p.1 p.2) (t0,y))
    (hD : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R, DifferentiableAt ℝ (G t) y)
    (hmod : ∀ η > 0, ∃ r > 0, r ≤ R ∧
      ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 r,
        ‖fderiv ℝ (G t) y-fderiv ℝ (G t) x0‖ ≤ η) :
    ContinuousAt (fun p : T × E => fderiv ℝ (G p.1) p.2) (t0,x0) := by
  have hcenter : ContinuousAt (fun t => fderiv ℝ (G t) x0) t0 := by
    change Tendsto _ (𝓝 t0) (𝓝 (fderiv ℝ (G t0) x0))
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨r,hr,hrR,hosc⟩ := hmod (ε/8) (by positivity)
    have hsub : closedBall x0 r ⊆ closedBall x0 R := closedBall_subset_closedBall hrR
    have hv := compact_family_norm_close_of_local_joint_continuity
      (isCompact_closedBall x0 r) (fun y hy => hG y (hsub hy)) (show 0 < ε*r/8 by positivity)
    filter_upwards [hv,hD,hosc] with t ht hdt hot
    have hh := fderiv_distance_le_of_value_and_derivative_oscillation hr
      (show 0 ≤ ε*r/8 by positivity) (show 0 ≤ ε/8 by positivity)
      (fun y hy => hdt y (hsub hy)) (fun y hy => hD.self_of_nhds y (hsub hy))
      hot hosc.self_of_nhds (fun y hy => (ht y hy).le)
    have he : 2*(ε/8)+2*(ε*r/8)/r = ε/2 := by field_simp [hr.ne'] <;> ring
    rw [he] at hh
    rw [dist_eq_norm]
    exact hh.trans_lt (by linarith)
  change Tendsto _ (𝓝 (t0,x0)) (𝓝 (fderiv ℝ (G t0) x0))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,_,hosc⟩ := hmod (ε/4) (by positivity)
  have hc := (Metric.tendsto_nhds.mp hcenter.tendsto) (ε/2) (by positivity)
  filter_upwards [continuousAt_fst.tendsto.eventually hc,
    continuousAt_fst.tendsto.eventually hosc,
    continuousAt_snd.tendsto.eventually (ball_mem_nhds x0 hr)] with p hp ho hy
  have hh := ho p.2 (ball_subset_closedBall hy)
  have hdist : dist (fderiv ℝ (G p.1) p.2) (fderiv ℝ (G p.1) x0) ≤ ε/4 := by
    simpa only [dist_eq_norm] using hh
  exact (dist_triangle (fderiv ℝ (G p.1) p.2) (fderiv ℝ (G p.1) x0)
    (fderiv ℝ (G t0) x0)).trans_lt (by linarith)

end PowerConvexity
