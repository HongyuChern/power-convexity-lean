import PowerConvexity.Analysis.ActualLocalHolderContinuityFour

/-! # Gluing actual interior jets to their proved flat boundary values -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actualFlatBoundaryFootFour_continuous (N : E) : Continuous (actualFlatBoundaryFootFour N) := by
  unfold actualFlatBoundaryFootFour
  fun_prop

theorem actualFlatBoundaryFootFour_fixed {N x : E} (hx : inner ℝ N x=0) :
    actualFlatBoundaryFootFour N x=x := by
  simp only [actualFlatBoundaryFootFour,hx,zero_smul,sub_zero]

def actualFlatJetExtensionFour {Z : Type*} (N : E) (f g : E → Z) (x : E) : Z :=
  if 0 < inner ℝ N x then f x else g (actualFlatBoundaryFootFour N x)

theorem actual_flat_jet_extension_continuous_four {Z : Type*} [NormedAddCommGroup Z]
    {N : E} (hN : ‖N‖=1) {f g : E → Z}
    (hf : ContinuousOn f (actualFlatUpperBallFour N (1/4 : ℝ)))
    (hg : ContinuousOn g (actualFlatBoundaryDiskFour N)) {epsilon : ℝ} (he : 0 < epsilon)
    {w : ℝ → ℝ} (hw : ContinuousAt w 0) (hw0 : w 0=0)
    (herr : ∀ x ∈ actualFlatUpperBallFour N (1/4 : ℝ), inner ℝ N x < epsilon →
      ‖f x-g (actualFlatBoundaryFootFour N x)‖ ≤ w (inner ℝ N x)) :
    ContinuousOn (actualFlatJetExtensionFour N f g) (actualFlatClosedUpperBallFour N (1/8 : ℝ)) := by
  let K := actualFlatClosedUpperBallFour N (1/8 : ℝ)
  have hmap : MapsTo (actualFlatBoundaryFootFour N) K (actualFlatBoundaryDiskFour N) := by
    intro x hx
    have hn : ‖x‖ ≤ (1/8 : ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    have hh := actual_flat_boundary_foot_four hN x
    exact ⟨hh.1,hh.2.1.trans (hn.trans (by norm_num))⟩
  have hbase : ContinuousOn (fun x => g (actualFlatBoundaryFootFour N x)) K :=
    hg.comp (actualFlatBoundaryFootFour_continuous N).continuousOn hmap
  intro x hx
  have hxN : ‖x‖ < (1/4 : ℝ) :=
    (by simpa only [mem_closedBall,dist_zero_right] using hx.1 : ‖x‖ ≤ (1/8 : ℝ)).trans_lt (by norm_num)
  by_cases hxp : 0 < inner ℝ N x
  · have hxU : x ∈ actualFlatUpperBallFour N (1/4 : ℝ) :=
      ⟨by simpa only [mem_ball,dist_zero_right] using hxN,hxp⟩
    have hfc : ContinuousAt f x := hf.continuousAt ((actualFlatUpperBallFour_isOpen N (1/4 : ℝ)).mem_nhds hxU)
    have heq : actualFlatJetExtensionFour N f g =ᶠ[𝓝 x] f := by
      have hopen : IsOpen {z : E | 0 < inner ℝ N z} := isOpen_lt continuous_const (continuous_const.inner continuous_id)
      filter_upwards [hopen.mem_nhds hxp] with z hz
      simp only [actualFlatJetExtensionFour,if_pos hz]
    exact (hfc.congr_of_eventuallyEq heq).continuousWithinAt
  · have hx0 : inner ℝ N x=0 := le_antisymm (le_of_not_gt hxp) hx.2
    have hnormal : Tendsto (fun z : E => inner ℝ N z) (𝓝[K] x) (𝓝 (0 : ℝ)) := by
      simpa only [hx0] using ((continuous_const.inner continuous_id : Continuous (fun z : E => inner ℝ N z)).tendsto x).mono_left nhdsWithin_le_nhds
    have hwlim : Tendsto (fun z : E => w (inner ℝ N z)) (𝓝[K] x) (𝓝 (0 : ℝ)) := by
      simpa only [hw0,Function.comp_def] using hw.tendsto.comp hnormal
    have hnear : ∀ᶠ z : E in 𝓝[K] x, inner ℝ N z < epsilon := hnormal (Iio_mem_nhds he)
    have hb : ∀ᶠ z : E in 𝓝[K] x,
        ‖actualFlatJetExtensionFour N f g z-g (actualFlatBoundaryFootFour N z)‖ ≤ w (inner ℝ N z) := by
      filter_upwards [self_mem_nhdsWithin,hnear] with z hz hze
      by_cases hzp : 0 < inner ℝ N z
      · have hzN : ‖z‖ < (1/4 : ℝ) :=
          (by simpa only [mem_closedBall,dist_zero_right] using hz.1 : ‖z‖ ≤ (1/8 : ℝ)).trans_lt (by norm_num)
        simpa only [actualFlatJetExtensionFour,if_pos hzp] using
          herr z ⟨by simpa only [mem_ball,dist_zero_right] using hzN,hzp⟩ hze
      · have hz0 : inner ℝ N z=0 := le_antisymm (le_of_not_gt hzp) hz.2
        rw [actualFlatJetExtensionFour,if_neg hzp,sub_self,norm_zero,hz0,hw0]
    have hd : Tendsto (fun z => actualFlatJetExtensionFour N f g z-g (actualFlatBoundaryFootFour N z))
        (𝓝[K] x) (𝓝 (0 : Z)) := squeeze_zero_norm' hb hwlim
    have hs := hd.add (hbase x hx)
    change Tendsto (actualFlatJetExtensionFour N f g) (𝓝[K] x)
      (𝓝 (actualFlatJetExtensionFour N f g x))
    have he0 : actualFlatJetExtensionFour N f g x=g (actualFlatBoundaryFootFour N x) := if_neg hxp
    rw [he0]
    simpa only [sub_add_cancel,zero_add] using hs

end PowerConvexity
