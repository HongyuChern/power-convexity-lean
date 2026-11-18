import PowerConvexity.Analysis.ActualBoundaryFootFour

/-! # Continuous extension of actual interior jets using the true distance to the boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualDomainJetExtensionFour {Z : Type*} (U : Set E) (f g : E → Z) (x : E) : Z := by
  classical
  exact if x ∈ U then f x else g x

theorem actual_domain_jet_extension_continuous_four {Z : Type*} [NormedAddCommGroup Z]
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) {f g : E → Z}
    (hf : ContinuousOn f U) (hg : ContinuousOn g (frontier U))
    {epsilon : ℝ} (he : 0 < epsilon) {w : ℝ → ℝ}
    (hw : ContinuousAt w 0) (hw0 : w 0=0)
    (herr : ∀ x ∈ U, infDist x (frontier U) < epsilon →
      ‖f x-g (actualBoundaryFootOnDomainFour U hproper x)‖ ≤ w (infDist x (frontier U))) :
    ContinuousOn (actualDomainJetExtensionFour U f g) (closure U) := by
  intro c hc
  by_cases hci : c ∈ U
  · have hfc : ContinuousAt f c := hf.continuousAt (hU.mem_nhds hci)
    have heq : actualDomainJetExtensionFour U f g =ᶠ[𝓝 c] f := by
      filter_upwards [hU.mem_nhds hci] with x hx
      simp only [actualDomainJetExtensionFour,if_pos hx]
    exact (hfc.congr_of_eventuallyEq heq).continuousWithinAt
  have hcf : c ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hc,hci⟩
  have hbase : Tendsto (fun x => g (actualBoundaryFootOnDomainFour U hproper x))
      (𝓝[closure U] c) (𝓝 (g c)) :=
    Filter.Tendsto.comp (hg c hcf) (actual_boundary_foot_tendsto_four hU hproper hcf)
  have hdist : Tendsto (fun x : E => infDist x (frontier U)) (𝓝[closure U] c) (𝓝 (0 : ℝ)) := by
    simpa only [infDist_zero_of_mem hcf] using
      ((continuous_infDist_pt (frontier U)).tendsto c).mono_left
        (show 𝓝[closure U] c ≤ 𝓝 c from nhdsWithin_le_nhds)
  have hwlim : Tendsto (fun x : E => w (infDist x (frontier U))) (𝓝[closure U] c) (𝓝 (0 : ℝ)) := by
    simpa only [hw0,Function.comp_def] using hw.tendsto.comp hdist
  have hnear : ∀ᶠ x : E in 𝓝[closure U] c, infDist x (frontier U) < epsilon :=
    hdist (Iio_mem_nhds he)
  have hb : ∀ᶠ x : E in 𝓝[closure U] c,
      ‖actualDomainJetExtensionFour U f g x-g (actualBoundaryFootOnDomainFour U hproper x)‖ ≤
        w (infDist x (frontier U)) := by
    filter_upwards [self_mem_nhdsWithin,hnear] with x hx hxe
    by_cases hxi : x ∈ U
    · simpa only [actualDomainJetExtensionFour,if_pos hxi] using herr x hxi hxe
    · have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx,hxi⟩
      rw [actualDomainJetExtensionFour,if_neg hxi,actual_boundary_foot_fixed_four hU hproper hxf,
        sub_self,norm_zero,infDist_zero_of_mem hxf,hw0]
  have hd : Tendsto (fun x => actualDomainJetExtensionFour U f g x-
      g (actualBoundaryFootOnDomainFour U hproper x)) (𝓝[closure U] c) (𝓝 (0 : Z)) :=
    squeeze_zero_norm' hb hwlim
  have hs := hd.add hbase
  change Tendsto (actualDomainJetExtensionFour U f g) (𝓝[closure U] c)
    (𝓝 (actualDomainJetExtensionFour U f g c))
  rw [actualDomainJetExtensionFour,if_neg hci]
  simpa only [sub_add_cancel,zero_add] using hs

end PowerConvexity
