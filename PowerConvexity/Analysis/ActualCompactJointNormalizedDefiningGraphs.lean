import PowerConvexity.Analysis.ActualCompactRegularGraphFamily
import PowerConvexity.Calculus.ParameterFiberDerivative

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
local instance acjnDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acjnDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance acjnDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance acjnHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acjnHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance acjnHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_compact_joint_normalized_defining_graphs
    {K : Set (ℝ × E)} (hK : IsCompact K) {f : ℝ × E → ℝ}
    (hf : ∀ p ∈ K, ContDiffAt ℝ 3 f p) (hf0 : ∀ p ∈ K, f p=0) (B Z : ℝ) :
    ∃ R > 0, R ≤ 1 ∧ ∃ M > 0,
      ∀ p ∈ K, ∀ G : E →L[ℝ] E, ‖G‖ ≤ B → ∀ N : E, ‖N‖=1 →
      ∀ zeta : ℝ, |zeta| ≤ Z →
      (∀ v : E, zeta*fderiv ℝ (fun y => f (p.1,y)) p.2 (G v)=inner ℝ N v) →
      ∃ rho : E → ℝ, rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
        (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
        (∀ x ∈ closedBall (0 : E) R,
          ContDiffAt ℝ 3 rho x ∧ ‖fderiv ℝ rho x‖ ≤ M ∧
          ‖fderiv ℝ (fderiv ℝ rho) x‖ ≤ M ∧
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ rho)) x‖ ≤ M) ∧
        (∀ x ∈ closedBall (0 : E) R,
          (0 < zeta*f (p.1,p.2+G (x+rho x • N)) ↔ 0 < inner ℝ N x) ∧
          (zeta*f (p.1,p.2+G (x+rho x • N))=0 ↔ inner ℝ N x=0)) := by
  let P := (ℝ × E) × (E →L[ℝ] E) × E × ℝ
  let S : Set P := K ×ˢ closedBall (0 : E →L[ℝ] E) B ×ˢ
    sphere (0 : E) 1 ×ˢ closedBall (0 : ℝ) Z
  let D : (ℝ × E) → E →L[ℝ] ℝ := fun q => fderiv ℝ (fun y => f (q.1,y)) q.2
  let C : Set P := {p | p.2.2.2 • (D p.1).comp p.2.1=
    InnerProductSpace.toDual ℝ E p.2.2.1}
  have hS : IsCompact S := hK.prod ((isCompact_closedBall (0 : E →L[ℝ] E) B).prod
    ((isCompact_sphere (0 : E) 1).prod (isCompact_closedBall (0 : ℝ) Z)))
  have hD : ContinuousOn (fun p : P => D p.1) S := by
    intro p hp
    exact (((parameter_fiber_fderiv_contDiffAt (n := 2) (hf p.1 hp.1)).continuousAt).comp
      continuousAt_fst).continuousWithinAt
  have hG : Continuous (fun p : P => p.2.1) := continuous_snd.fst
  have hN : Continuous (fun p : P => p.2.2.1) := continuous_snd.snd.fst
  have hZ : Continuous (fun p : P => p.2.2.2) := continuous_snd.snd.snd
  have hSCc : IsClosed (S ∩ C) := hS.isClosed.isClosed_eq
    (hZ.continuousOn.smul (hD.clm_comp hG.continuousOn))
    (((InnerProductSpace.toDual ℝ E).continuous.comp hN).continuousOn)
  have hSC : IsCompact (S ∩ C) := hS.of_isClosed_subset hSCc inter_subset_left
  let N : P → E := fun p => p.2.2.1
  let F : P × E → ℝ := fun q => q.1.2.2.2*f (q.1.1.1,q.1.1.2+q.1.2.1 q.2)
  have hFN : ContDiff ℝ 3 N := contDiff_snd.snd.fst
  have hFt : ContDiff ℝ 3 (fun q : P × E => q.1.1.1) := contDiff_fst.fst.fst
  have hFc : ContDiff ℝ 3 (fun q : P × E => q.1.1.2) := contDiff_fst.fst.snd
  have hFG : ContDiff ℝ 3 (fun q : P × E => q.1.2.1) := contDiff_fst.snd.fst
  have hFZ : ContDiff ℝ 3 (fun q : P × E => q.1.2.2.2) := contDiff_fst.snd.snd.snd
  have hF (p : P) (hp : p ∈ S ∩ C) : ContDiffAt ℝ 3 F (p,0) := by
    have hc : ContDiffAt ℝ 3 f (p.1.1,p.1.2+p.2.1 0) := by
      simpa only [map_zero,add_zero,Prod.mk.eta] using hf p.1 hp.1.1
    exact hFZ.contDiffAt.mul (hc.comp (p,0)
      (hFt.prodMk (hFc.add (hFG.clm_apply contDiff_snd))).contDiffAt)
  have hNu (p : P) (hp : p ∈ S ∩ C) : ‖N p‖=1 := by
    simpa only [N,mem_sphere,dist_zero_right] using hp.1.2.2.1
  have hF0 (p : P) (hp : p ∈ S ∩ C) : F (p,0)=0 := by
    simp only [F,map_zero,add_zero,Prod.mk.eta,hf0 p.1 hp.1.1,mul_zero]
  have hDf (p : P) (hp : p ∈ S ∩ C) (v : E) :
      fderiv ℝ (fun y => F (p,y)) 0 v=inner ℝ (N p) v := by
    have hfc : ContDiffAt ℝ 3 (fun y => f (p.1.1,y)) p.1.2 :=
      (hf p.1 hp.1.1).comp p.1.2 (contDiffAt_const.prodMk contDiffAt_id)
    have hfAt : HasFDerivAt (fun y => f (p.1.1,y)) (D p.1) (p.1.2+p.2.1 0) := by
      simpa only [D,map_zero,add_zero] using (hfc.differentiableAt (by norm_num)).hasFDerivAt
    have htrans : HasFDerivAt (fun y => p.1.2+p.2.1 y) p.2.1 0 :=
      p.2.1.hasFDerivAt.const_add p.1.2
    have hfd : HasFDerivAt (fun y => F (p,y))
        (p.2.2.2 • (D p.1).comp p.2.1) 0 :=
      (hfAt.comp 0 htrans).const_smul p.2.2.2
    rw [hfd.fderiv]
    have he := hp.2
    change p.2.2.2 • (D p.1).comp p.2.1=InnerProductSpace.toDual ℝ E p.2.2.1 at he
    rw [he]
    rfl
  obtain ⟨R,hR,hR1,M,hM,hgraphs⟩ := actual_compact_regular_graph_family hSC
    (fun p _ => hFN.contDiffAt) hF hNu hF0 hDf
  refine ⟨R,hR,hR1,M,hM,?_⟩
  intro q hq G hGB n hn zeta hz hDnorm
  let p : P := (q,G,n,zeta)
  have hpS : p ∈ S := ⟨hq,
    by simpa only [mem_closedBall,dist_zero_right] using hGB,
    by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hz⟩
  have hpC : p ∈ C := by
    apply ContinuousLinearMap.ext
    intro v
    exact hDnorm v
  exact hgraphs p ⟨hpS,hpC⟩

end PowerConvexity
