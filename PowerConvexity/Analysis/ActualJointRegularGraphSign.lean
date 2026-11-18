import PowerConvexity.Analysis.ActualJointRegularLevelGraphFour
import PowerConvexity.Analysis.ActualJointNormalLineSign

/-! # The actual joint regular-level graph has the correct domain side -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_joint_regular_graph_sign
    {s : P} {N : P → E} {f : P × E → ℝ}
    (hN : ContDiffAt ℝ 3 N s) (hf : ContDiffAt ℝ 3 f (s,0))
    (hNs : ‖N s‖=1) (hfs : f (s,0)=0)
    (hDfs : ∀ v : E, fderiv ℝ (fun y => f (s,y)) 0 v=inner ℝ (N s) v) :
    ∃ rho : P × E → ℝ, ContDiffAt ℝ 3 rho (s,0) ∧
      (∀ p : P, ‖N p‖=1 → ∀ x : E, ∀ t : ℝ,
        rho (p,x+t • N p)=rho (p,x)) ∧
      (∀ᶠ p in 𝓝 s, ‖N p‖=1 → f (p,0)=0 →
        (∀ v : E, fderiv ℝ (fun y => f (p,y)) 0 v=inner ℝ (N p) v) →
        rho (p,0)=0 ∧ fderiv ℝ (fun y => rho (p,y)) 0=0) ∧
      (∀ᶠ q in 𝓝 (s,0), ‖N q.1‖=1 →
        (0 < f (q.1,q.2+rho q • N q.1) ↔ 0 < inner ℝ (N q.1) q.2) ∧
        (f (q.1,q.2+rho q • N q.1)=0 ↔ inner ℝ (N q.1) q.2=0) ∧
        (f (q.1,q.2+rho q • N q.1) < 0 ↔ inner ℝ (N q.1) q.2 < 0)) := by
  obtain ⟨rho,hrho,hinv,hcenter,hzero⟩ := actual_joint_regular_level_graph hN hf hNs hfs hDfs
  have hrho0 : rho (s,0)=0 := (hcenter.self_of_nhds hNs hfs hDfs).1
  have hDN : fderiv ℝ (fun y => f (s,y)) 0 (N s)=1 := by
    rw [hDfs,real_inner_self_eq_norm_sq,hNs]
    norm_num
  obtain ⟨V,hVo,hV,hSign⟩ := actual_joint_normal_line_sign hN.continuousAt
    (hf.of_le (by norm_num)) hDN
  let gamma : P × E → E := fun q => q.2-inner ℝ (N q.1) q.2 • N q.1+rho q • N q.1
  let Phi : P × E → E := fun q => q.2+rho q • N q.1
  have hNp : ContDiffAt ℝ 3 (fun q : P × E => N q.1) (s,0) :=
    hN.comp (s,0) contDiffAt_fst
  have hgamma : ContDiffAt ℝ 3 gamma (s,0) :=
    (contDiffAt_snd.sub ((hNp.inner ℝ contDiffAt_snd).smul hNp)).add (hrho.smul hNp)
  have hPhi : ContDiffAt ℝ 3 Phi (s,0) := contDiffAt_snd.add (hrho.smul hNp)
  have hgamma0 : gamma (s,0)=0 := by
    simp only [gamma,hrho0,inner_zero_right,zero_smul,sub_zero,add_zero]
  have hPhi0 : Phi (s,0)=0 := by simp only [Phi,hrho0,zero_smul,add_zero]
  have hgt : Tendsto (fun q : P × E => (q.1,gamma q)) (𝓝 (s,0)) (𝓝 (s,0)) := by
    have hh := (contDiffAt_fst.prodMk hgamma).continuousAt
    change Tendsto _ _ (𝓝 (s,gamma (s,0))) at hh
    simpa only [hgamma0] using hh
  have hpt : Tendsto (fun q : P × E => (q.1,Phi q)) (𝓝 (s,0)) (𝓝 (s,0)) := by
    have hh := (contDiffAt_fst.prodMk hPhi).continuousAt
    change Tendsto _ _ (𝓝 (s,Phi (s,0))) at hh
    simpa only [hPhi0] using hh
  refine ⟨rho,hrho,hinv,hcenter,?_⟩
  filter_upwards [hzero,hgt.eventually (hVo.mem_nhds hV),hpt.eventually (hVo.mem_nhds hV)] with q hz hgz hpz
  intro hq
  have he : Phi q-gamma q=inner ℝ (N q.1) q.2 • N q.1 := by
    dsimp only [Phi,gamma]
    abel
  exact hSign q.1 hq (Phi q) hpz (gamma q) hgz (inner ℝ (N q.1) q.2) he (hz hq)

end PowerConvexity
