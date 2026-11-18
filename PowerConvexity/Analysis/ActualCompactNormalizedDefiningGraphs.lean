import PowerConvexity.Analysis.ActualCompactRegularGraphFamily

/-! # Actual uniform defining graphs for all bounded linear normalizations

The compact parameter set contains the real boundary point, actual linear
map, actual unit normal and scalar defining-function normalization. Its closed
constraint is the genuine normalized differential identity. No continuity of
a spectral choice of normalizing maps is needed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
local instance acndDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acndDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance acndDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance acndHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acndHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance acndHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_compact_bounded_normalized_defining_graphs
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ c ∈ K, f c=0) (B Z : ℝ) :
    ∃ R > 0, R ≤ 1 ∧ ∃ M > 0,
      ∀ c ∈ K, ∀ G : E →L[ℝ] E, ‖G‖ ≤ B → ∀ N : E, ‖N‖=1 →
      ∀ zeta : ℝ, |zeta| ≤ Z →
      (∀ v : E, zeta*fderiv ℝ f c (G v)=inner ℝ N v) →
      ∃ rho : E → ℝ, rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
        (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
        (∀ x ∈ closedBall (0 : E) R,
          ContDiffAt ℝ 3 rho x ∧ ‖fderiv ℝ rho x‖ ≤ M ∧
          ‖fderiv ℝ (fderiv ℝ rho) x‖ ≤ M ∧
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ rho)) x‖ ≤ M) ∧
        (∀ x ∈ closedBall (0 : E) R,
          (0 < zeta*f (c+G (x+rho x • N)) ↔ 0 < inner ℝ N x) ∧
          (zeta*f (c+G (x+rho x • N))=0 ↔ inner ℝ N x=0)) := by
  let P := E × (E →L[ℝ] E) × E × ℝ
  let S : Set P := K ×ˢ closedBall (0 : E →L[ℝ] E) B ×ˢ
    sphere (0 : E) 1 ×ˢ closedBall (0 : ℝ) Z
  let C : Set P := {p | p.2.2.2 • (fderiv ℝ f p.1).comp p.2.1=
    InnerProductSpace.toDual ℝ E p.2.2.1}
  have hS : IsCompact S := hK.prod ((isCompact_closedBall (0 : E →L[ℝ] E) B).prod
    ((isCompact_sphere (0 : E) 1).prod (isCompact_closedBall (0 : ℝ) Z)))
  have hD : Continuous (fun p : P => fderiv ℝ f p.1) :=
    (hf.fderiv_right (m := 2) (by norm_num)).continuous.comp continuous_fst
  have hG : Continuous (fun p : P => p.2.1) := continuous_snd.fst
  have hN : Continuous (fun p : P => p.2.2.1) := continuous_snd.snd.fst
  have hZ : Continuous (fun p : P => p.2.2.2) := continuous_snd.snd.snd
  have hC : IsClosed C := isClosed_eq (hZ.smul (hD.clm_comp hG))
    ((InnerProductSpace.toDual ℝ E).continuous.comp hN)
  have hSC : IsCompact (S ∩ C) := hS.inter_right hC
  let N : P → E := fun p => p.2.2.1
  let F : P × E → ℝ := fun q => q.1.2.2.2*f (q.1.1+q.1.2.1 q.2)
  have hFN : ContDiff ℝ 3 N := contDiff_snd.snd.fst
  have hFc : ContDiff ℝ 3 (fun q : P × E => q.1.1) := contDiff_fst.fst
  have hFG : ContDiff ℝ 3 (fun q : P × E => q.1.2.1) := contDiff_fst.snd.fst
  have hFZ : ContDiff ℝ 3 (fun q : P × E => q.1.2.2.2) := contDiff_fst.snd.snd.snd
  have hF : ContDiff ℝ 3 F := hFZ.mul (hf.comp (hFc.add (hFG.clm_apply contDiff_snd)))
  have hNu (p : P) (hp : p ∈ S ∩ C) : ‖N p‖=1 := by
    simpa only [N,mem_sphere,dist_zero_right] using hp.1.2.2.1
  have hF0 (p : P) (hp : p ∈ S ∩ C) : F (p,0)=0 := by
    simp only [F,map_zero,add_zero,hf0 p.1 hp.1.1,mul_zero]
  have hDf (p : P) (hp : p ∈ S ∩ C) (v : E) :
      fderiv ℝ (fun y => F (p,y)) 0 v=inner ℝ (N p) v := by
    have hfAt : HasFDerivAt f (fderiv ℝ f p.1) (p.1+p.2.1 0) := by
      simpa only [map_zero,add_zero] using (hf.differentiable (by norm_num) p.1).hasFDerivAt
    have htrans : HasFDerivAt (fun y => p.1+p.2.1 y) p.2.1 0 :=
      p.2.1.hasFDerivAt.const_add p.1
    have hfd : HasFDerivAt (fun y => F (p,y))
        (p.2.2.2 • (fderiv ℝ f p.1).comp p.2.1) 0 :=
      (hfAt.comp 0 htrans).const_smul p.2.2.2
    rw [hfd.fderiv]
    have he := hp.2
    change p.2.2.2 • (fderiv ℝ f p.1).comp p.2.1=InnerProductSpace.toDual ℝ E p.2.2.1 at he
    rw [he]
    rfl
  obtain ⟨R,hR,hR1,M,hM,hgraphs⟩ := actual_compact_regular_graph_family hSC
    (fun p _ => hFN.contDiffAt) (fun p _ => hF.contDiffAt) hNu hF0 hDf
  refine ⟨R,hR,hR1,M,hM,?_⟩
  intro c hc G hGB n hn zeta hz hDnorm
  let p : P := (c,G,n,zeta)
  have hpS : p ∈ S := ⟨hc,
    by simpa only [mem_closedBall,dist_zero_right] using hGB,
    by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hz⟩
  have hpC : p ∈ C := by
    apply ContinuousLinearMap.ext
    intro v
    exact hDnorm v
  exact hgraphs p ⟨hpS,hpC⟩

end PowerConvexity
