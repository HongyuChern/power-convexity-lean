import PowerConvexity.Calculus.ConvexFamilyFirstJetContinuity
import PowerConvexity.Calculus.PowerInitialConvexityTwo

/-! # Joint first jets of the actual power transform on varying physical domains -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]

theorem powerFamily_fderiv_continuousAt_of_joint_values
    {U : T → Set E} {u : T → E → ℝ}
    (hU : ∀ t, IsOpen (U t))
    (hZ : Continuous (fun p : T × E => (U p.1).indicator (u p.1) p.2))
    (hu : ∀ t, ContDiffOn ℝ 2 (u t) (U t))
    (hneg : ∀ t, ∀ y ∈ U t, u t y < 0)
    (hconv : ∀ t, ConvexOn ℝ (U t) (powerTransform (u t)))
    {t0 : T} {x0 : E} (hx : x0 ∈ U t0)
    {R : ℝ} (hR : 0 < R)
    (hball : ∀ᶠ t in 𝓝 t0, closedBall x0 R ⊆ U t) :
    ContinuousAt (fun p : T × E => fderiv ℝ (powerTransform (u p.1)) p.2) (t0,x0) := by
  let F : T → E → ℝ := fun t => powerTransform ((U t).indicator (u t))
  have hF : Continuous (fun p : T × E => F p.1 p.2) := by
    exact (Real.continuous_sqrt.comp hZ.neg).neg
  have heq (t : T) (y : E) (hy : y ∈ U t) :
      F t =ᶠ[𝓝 y] powerTransform (u t) := by
    filter_upwards [(hU t).mem_nhds hy] with z hz
    simp only [F,powerTransform,Set.indicator_of_mem hz]
  have hreg (t : T) (y : E) (hy : y ∈ U t) :
      ContDiffAt ℝ 2 (F t) y :=
    (powerTransform_contDiffAt ((hu t).contDiffAt ((hU t).mem_nhds hy))
      (hneg t y hy)).congr_of_eventuallyEq (heq t y hy)
  have hFc : ∀ᶠ t in 𝓝 t0, ConvexOn ℝ (closedBall x0 R) (F t) ∧
      ∀ y ∈ ball x0 R, DifferentiableAt ℝ (F t) y := by
    filter_upwards [hball] with t ht
    refine ⟨?_,fun y hy => (hreg t y (ht (ball_subset_closedBall hy))).differentiableAt (by norm_num)⟩
    apply ((hconv t).subset ht (convex_closedBall x0 R)).congr
    intro y hy
    simp only [F,powerTransform,Set.indicator_of_mem (ht hy)]
  have hD := convexFamily_fderiv_continuousAt_of_joint_values hF (hreg t0 x0 hx) hR hFc
  apply hD.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually hball,
    continuousAt_snd.tendsto.eventually (ball_mem_nhds x0 hR)] with p hp hy
  exact (heq p.1 p.2 (hp (ball_subset_closedBall hy))).fderiv_eq.symm

theorem original_fderiv_from_power {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hx : u x < 0) :
    fderiv ℝ u x = (-2*powerTransform u x) • fderiv ℝ (powerTransform u) x := by
  rw [fderiv_powerTransform hu hx,smul_smul]
  have hs : Real.sqrt (-u x) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hx)).ne'
  have hc : (-2*powerTransform u x)*sqrtSlope (u x) = 1 := by
    dsimp only [powerTransform,negativeSqrt,sqrtSlope]
    field_simp [hs]
    <;> ring
  rw [hc,one_smul]

theorem originalFamily_fderiv_continuousAt_of_power_firstJet
    {U : T → Set E} {u : T → E → ℝ}
    (hZ : Continuous (fun p : T × E => (U p.1).indicator (u p.1) p.2))
    (hu : ∀ t, ∀ y ∈ U t, DifferentiableAt ℝ (u t) y)
    (hneg : ∀ t, ∀ y ∈ U t, u t y < 0)
    {t0 : T} {x0 : E}
    (hmem : ∀ᶠ p : T × E in 𝓝 (t0,x0), p.2 ∈ U p.1)
    (hD : ContinuousAt (fun p : T × E => fderiv ℝ (powerTransform (u p.1)) p.2) (t0,x0)) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,x0) := by
  have hP : ContinuousAt (fun p : T × E => powerTransform (u p.1) p.2) (t0,x0) := by
    have hzero : Continuous (fun p : T × E => powerTransform ((U p.1).indicator (u p.1)) p.2) :=
      (Real.continuous_sqrt.comp hZ.neg).neg
    apply hzero.continuousAt.congr_of_eventuallyEq
    filter_upwards [hmem] with p hp
    simp only [powerTransform,Set.indicator_of_mem hp]
  have hh : ContinuousAt (fun p : T × E =>
      (-2 * powerTransform (u p.1) p.2) • fderiv ℝ (powerTransform (u p.1)) p.2) (t0,x0) :=
    (continuousAt_const.mul hP).smul hD
  apply hh.congr_of_eventuallyEq
  filter_upwards [hmem] with p hp
  exact original_fderiv_from_power (hu p.1 p.2 hp) (hneg p.1 p.2 hp)

end PowerConvexity
