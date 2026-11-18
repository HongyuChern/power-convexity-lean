import PowerConvexity.Calculus.ConvexFirstDerivativeBound
import PowerConvexity.Analysis.CompactSmallParameter

/-! # Local joint first-jet continuity from convexity and joint value continuity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

section CompactValues
variable {T E : Type*} [TopologicalSpace T] [TopologicalSpace E]

theorem compact_family_value_close {F : T → E → ℝ}
    (hF : Continuous (fun p : T × E => F p.1 p.2))
    {K : Set E} (hK : IsCompact K) (t0 : T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t0, ∀ y ∈ K, |F t y-F t0 y| < ε := by
  apply hK.eventually_forall_of_forall_eventually
  intro y _
  have hg : Continuous (fun p : T × E => |F p.1 p.2-F t0 p.2|) := by
    exact (hF.sub (hF.comp (continuous_const.prodMk continuous_snd))).abs
  have hzero : |F t0 y-F t0 y| < ε := by simpa using hε
  exact hg.continuousAt.tendsto.eventually (gt_mem_nhds hzero)

end CompactValues
variable {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]

theorem convexFamily_fderiv_continuousAt_of_joint_values
    {F : T → E → ℝ} (hF : Continuous (fun p : T × E => F p.1 p.2))
    {t0 : T} {x0 : E} (hg : ContDiffAt ℝ 2 (F t0) x0)
    {R : ℝ} (hR : 0 < R)
    (hconv : ∀ᶠ t in 𝓝 t0, ConvexOn ℝ (closedBall x0 R) (F t) ∧
      ∀ y ∈ ball x0 R, DifferentiableAt ℝ (F t) y) :
    ContinuousAt (fun p : T × E => fderiv ℝ (F p.1) p.2) (t0,x0) := by
  change Tendsto _ (𝓝 (t0,x0)) (𝓝 (fderiv ℝ (F t0) x0))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C,hC,S,hS,hgS,hHS⟩ := exists_local_uniform_Hessian_bound hg
  let r := min R S
  have hr : 0 < r := lt_min hR hS
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := min_le_right _ _
  let t := min (r/4) (ε/(4*(C+1)))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htr : t ≤ r/2 := (min_le_left _ _).trans (by linarith)
  have htε : C*t ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (r/4) (ε/(4*(C+1)))) hC.le
    have hc1 : 0 < C+1 := by linarith
    have hh' : C*(ε/(4*(C+1))) ≤ ε/4 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
      have hden : 0 < 4*(C+1) := by positivity
      have hcancel : (4*(C*(ε/(4*(C+1)))))*(C+1) = C*ε := by
        field_simp [hc1.ne']
        <;> ring
      have hmul : (4*(C*(ε/(4*(C+1)))))*(C+1) ≤ ε*(C+1) := by
        rw [hcancel]
        nlinarith
      have hs : 4*(C*(ε/(4*(C+1)))) ≤ ε :=
        (mul_le_mul_iff_left₀ hc1).mp hmul
      nlinarith only [hs]
    exact hh.trans hh'
  let δ := ε*t/8
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : 2*δ/t = ε/4 := by dsimp only [δ]; field_simp [ht.ne'] <;> ring
  have hval := compact_family_value_close hF (isCompact_closedBall x0 r) t0 hδ
  have hDg : ContinuousAt (fderiv ℝ (F t0)) x0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hclose := (Metric.tendsto_nhds.mp hDg.tendsto) (ε/2) (by positivity)
  have hyball : ∀ᶠ p : T × E in 𝓝 (t0,x0), p.2 ∈ ball x0 (r/2) :=
    continuousAt_snd.tendsto.eventually (ball_mem_nhds x0 (by positivity))
  filter_upwards [continuousAt_fst.tendsto.eventually hval,
    continuousAt_fst.tendsto.eventually hconv,
    continuousAt_snd.tendsto.eventually hclose,hyball] with p hpval hpconv hpclose hpy
  have hpR : p.2 ∈ ball x0 R := (ball_subset_ball (by linarith : r/2 ≤ R)) hpy
  have hballsub : closedBall x0 r ⊆ closedBall x0 R := closedBall_subset_closedBall hrR
  have hSsub : closedBall x0 r ⊆ closedBall x0 S := closedBall_subset_closedBall hrS
  have hbound := convex_fderiv_distance_le_of_value_bound hr hC.le hδ.le ht htr
    (hpconv.1.subset hballsub (convex_closedBall x0 r)) (hpconv.2 _ hpR)
    (fun z hz => hgS z (hSsub hz)) (fun z hz => hHS z (hSsub hz))
    (fun z hz => (hpval z hz).le) hpy
  rw [hδeq] at hbound
  have hhalf : dist (fderiv ℝ (F p.1) p.2) (fderiv ℝ (F t0) p.2) ≤ ε/2 := by
    rw [dist_eq_norm]
    linarith
  exact (dist_triangle (fderiv ℝ (F p.1) p.2) (fderiv ℝ (F t0) p.2)
    (fderiv ℝ (F t0) x0)).trans_lt (by linarith)

end PowerConvexity
