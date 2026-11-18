import PowerConvexity.Analysis.ActualRegularLevelGraphFour
import PowerConvexity.Analysis.ActualNormalLineSignFour

/-! # The constructed graph maps the positive half-space into the true domain side -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_regular_graph_sign_four {N : E} (hN : ‖N‖=1) {f : E → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hDf : ∀ v : E, fderiv ℝ f 0 v=inner ℝ N v) :
    ∃ rho : E → ℝ, ContDiffAt ℝ 3 rho 0 ∧ rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
      ∀ᶠ z : E in 𝓝 0,
        (0 < f (actualGraphShearFour N rho z) ↔ 0 < inner ℝ N z) ∧
        (f (actualGraphShearFour N rho z)=0 ↔ inner ℝ N z=0) ∧
        (f (actualGraphShearFour N rho z) < 0 ↔ inner ℝ N z < 0) := by
  obtain ⟨rho,hrho,hrho0,hD0,hinv,hzero⟩ := actual_regular_level_graph_four hN hf hf0 hDf
  have hDN : fderiv ℝ f 0 N=1 := by rw [hDf N,real_inner_self_eq_norm_sq,hN]; norm_num
  obtain ⟨V,hVo,h0V,hSign⟩ := actual_normal_line_sign hN (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)) hDN
  let gamma : E → E := fun z => z-inner ℝ N z • N+rho z • N
  have hgamma0 : gamma 0=0 := by simp only [gamma,inner_zero_right,hrho0,zero_smul,sub_zero,add_zero]
  have hgammaC : ContinuousAt gamma 0 := by
    have hn : Continuous (fun z : E => inner ℝ N z) := continuous_const.inner continuous_id
    have hs : ContinuousAt (fun z : E => inner ℝ N z • N) 0 := hn.continuousAt.smul continuousAt_const
    have ht : ContinuousAt (fun z : E => rho z • N) 0 := hrho.continuousAt.smul continuousAt_const
    exact (continuousAt_id.sub hs).add ht
  have hPhi0 : actualGraphShearFour N rho 0=0 := by simp only [actualGraphShearFour,hrho0,zero_smul,add_zero]
  have hPhiC := (actual_graph_shear_contDiffAt_four (N := N) hrho).continuousAt
  have hgt : Tendsto gamma (𝓝 (0 : E)) (𝓝 (0 : E)) := by simpa only [hgamma0] using hgammaC.tendsto
  have hpt : Tendsto (actualGraphShearFour N rho) (𝓝 (0 : E)) (𝓝 (0 : E)) := by simpa only [hPhi0] using hPhiC.tendsto
  refine ⟨rho,hrho,hrho0,hD0,hinv,?_⟩
  filter_upwards [hzero,hgt.eventually (hVo.mem_nhds h0V),hpt.eventually (hVo.mem_nhds h0V)] with z hz hgz hpz
  have he : actualGraphShearFour N rho z-gamma z=inner ℝ N z • N := by
    dsimp [actualGraphShearFour,gamma]
    abel
  exact hSign _ hpz _ hgz (inner ℝ N z) he hz

theorem actual_regular_domain_graph_four {U : Set E} {N : E} (hN : ‖N‖=1) {f : E → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hDf : ∀ v : E, fderiv ℝ f 0 v=inner ℝ N v)
    (hdef : ∀ᶠ y : E in 𝓝 0, y ∈ U ↔ 0 < f y) :
    ∃ rho : E → ℝ, ContDiffAt ℝ 3 rho 0 ∧ rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
      ∃ R > 0, R ≤ 1 ∧ ∀ z ∈ closedBall (0 : E) R,
        actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z := by
  obtain ⟨rho,hrho,hrho0,hD0,hinv,hSign⟩ := actual_regular_graph_sign_four hN hf hf0 hDf
  have hPhi0 : actualGraphShearFour N rho 0=0 := by simp only [actualGraphShearFour,hrho0,zero_smul,add_zero]
  have ht : Tendsto (actualGraphShearFour N rho) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [hPhi0] using (actual_graph_shear_contDiffAt_four (N := N) hrho).continuousAt.tendsto
  have hnear : ∀ᶠ z : E in 𝓝 0, actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z := by
    filter_upwards [hSign,ht.eventually hdef] with z hz hdz
    exact hdz.trans hz.1
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min 1 (d/2)
  have hR : 0 < R := lt_min zero_lt_one (half_pos hd)
  refine ⟨rho,hrho,hrho0,hD0,hinv,R,hR,min_le_left _ _,?_⟩
  intro z hz
  apply hball
  have hzR : dist z 0 ≤ R := hz
  have hRd : R ≤ d/2 := min_le_right _ _
  change dist z 0 < d
  linarith

end PowerConvexity
