import PowerConvexity.Analysis.ActualRegularLevelGraphFour
import PowerConvexity.Calculus.FiniteParameterGraphLocalInverse

/-! # Actual regular-level graphs depending jointly on normalization parameters

The finite-dimensional parameter may contain the boundary point, normal and
linear coefficient normalization. One total inverse supplies a jointly C3
height. Centering and vanishing first derivative hold at every nearby
parameter satisfying the actual level and differential constraints.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_regular_level_map_fiber_derivative
    {N : E} {f : E → ℝ} (hf : DifferentiableAt ℝ f 0)
    (hDf : ∀ v : E, fderiv ℝ f 0 v=inner ℝ N v) :
    HasFDerivAt (fun y => y+(f y-inner ℝ N y) • N)
      (ContinuousLinearMap.id ℝ E) 0 := by
  let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E N
  have hDl : fderiv ℝ f 0=l := by ext v; exact hDf v
  have hh := (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).add
    ((hf.hasFDerivAt.sub l.hasFDerivAt).smul_const N)
  change HasFDerivAt (fun y => y+(f y-l y) • N) (ContinuousLinearMap.id ℝ E) 0
  simpa only [hDl,Pi.add_def,Pi.sub_def,Function.comp_def,id_eq,sub_self,
    ContinuousLinearMap.zero_smulRight,add_zero] using hh

theorem actual_joint_regular_level_graph
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
        f (q.1,q.2-inner ℝ (N q.1) q.2 • N q.1+rho q • N q.1)=0) := by
  let F : P × E → E := fun q => q.2+(f q-inner ℝ (N q.1) q.2) • N q.1
  have hNp : ContDiffAt ℝ 3 (fun q : P × E => N q.1) (s,0) :=
    hN.comp (s,0) contDiffAt_fst
  have hF : ContDiffAt ℝ 3 F (s,0) :=
    contDiffAt_snd.add ((hf.sub (hNp.inner ℝ contDiffAt_snd)).smul hNp)
  have hff : ContDiffAt ℝ 3 (fun y => f (s,y)) 0 :=
    hf.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hFd : fderiv ℝ (fun y => F (s,y)) 0=ContinuousLinearMap.id ℝ E :=
    (actual_regular_level_map_fiber_derivative (hff.differentiableAt (by norm_num)) hDfs).fderiv
  have hF0 : F (s,0)=0 := by simp only [F,hfs,inner_zero_right,sub_self,zero_smul,add_zero]
  obtain ⟨g,hg,hg0,hright,hleft⟩ := exists_finite_parameter_preserving_C3_localInverse hF
    (by rw [hFd]; exact Function.injective_id)
  rw [hF0] at hg hg0 hright
  let Q : P × E → E := fun q => q.2-inner ℝ (N q.1) q.2 • N q.1
  have hQ : ContDiffAt ℝ 3 Q (s,0) :=
    contDiffAt_snd.sub ((hNp.inner ℝ contDiffAt_snd).smul hNp)
  have hQ0 : Q (s,0)=0 := by simp only [Q,inner_zero_right,zero_smul,sub_zero]
  have hgQ : ContDiffAt ℝ 3 (fun q => g (q.1,Q q)) (s,0) := by
    have hgg : ContDiffAt ℝ 3 g (s,Q (s,0)) := by simpa only [hQ0] using hg
    exact hgg.comp (s,0) (contDiffAt_fst.prodMk hQ)
  let rho : P × E → ℝ := fun q => inner ℝ (N q.1) (g (q.1,Q q))
  have hrho : ContDiffAt ℝ 3 rho (s,0) := hNp.inner ℝ hgQ
  have hnc : Tendsto (fun p : P => (p,(0 : E))) (𝓝 s) (𝓝 (s,0)) :=
    (continuous_id.prodMk continuous_const).tendsto s
  have hleftc : ∀ᶠ p in 𝓝 s, ∀ᶠ y in 𝓝 (0 : E), g (p,F (p,y))=y :=
    (show ∀ᶠ q in 𝓝 s ×ˢ 𝓝 (0 : E), g (q.1,F q)=q.2 from by
      simpa only [nhds_prod_eq] using hleft).curry
  refine ⟨rho,hrho,?_,?_,?_⟩
  · intro p hp x t
    have hn : inner ℝ (N p) (N p)=1 := by rw [real_inner_self_eq_norm_sq,hp]; norm_num
    have he : Q (p,x+t • N p)=Q (p,x) := by
      dsimp only [Q]
      rw [inner_add_right,inner_smul_right,hn,mul_one,add_smul]
      abel
    simp only [rho,he]
  · filter_upwards [hnc.eventually (hf.eventually (by norm_num)),
      hnc.eventually (hg.eventually (by norm_num)),hleftc] with p hfp hgp hlp
    intro hp hf0 hdf
    have hFp0 : F (p,0)=0 := by simp only [F,hf0,inner_zero_right,sub_self,zero_smul,add_zero]
    have hgp0 : g (p,0)=0 := by simpa only [hFp0] using hlp.self_of_nhds
    have hfp' : ContDiffAt ℝ 3 (fun y => f (p,y)) 0 :=
      hfp.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
    have hgp' : ContDiffAt ℝ 3 (fun y => g (p,y)) 0 :=
      hgp.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
    have hFpd : HasFDerivAt (fun y => F (p,y)) (ContinuousLinearMap.id ℝ E) 0 :=
      actual_regular_level_map_fiber_derivative (hfp'.differentiableAt (by norm_num)) hdf
    let Dg := fderiv ℝ (fun y => g (p,y)) 0
    have hgd : HasFDerivAt (fun y => g (p,y)) Dg (F (p,0)) := by
      rw [hFp0]
      exact (hgp'.differentiableAt (by norm_num)).hasFDerivAt
    have hcomp : HasFDerivAt (fun y => g (p,F (p,y))) Dg 0 := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hgd.comp 0 hFpd
    have hDi : Dg=ContinuousLinearMap.id ℝ E := by
      have heq : (fun y => g (p,F (p,y))) =ᶠ[𝓝 (0 : E)] (fun y => y) := hlp
      rw [← hcomp.fderiv,heq.fderiv_eq]
      exact fderiv_id
    let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (N p)
    let T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-l.smulRight (N p)
    have hT (y : E) : T y=Q (p,y) := rfl
    have hlT (y : E) : l (T y)=0 := by
      change inner ℝ (N p) (y-inner ℝ (N p) y • N p)=0
      rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hp]
      norm_num
    have hDg0 : HasFDerivAt (fun y => g (p,y)) (ContinuousLinearMap.id ℝ E) (T 0) := by
      rw [map_zero,← hDi]
      exact (hgp'.differentiableAt (by norm_num)).hasFDerivAt
    have hDgT : HasFDerivAt (fun y => g (p,T y)) T 0 := by
      simpa only [Function.comp_def,ContinuousLinearMap.id_comp] using hDg0.comp 0 T.hasFDerivAt
    have hDrho : HasFDerivAt (fun y => rho (p,y)) (l.comp T) 0 :=
      l.hasFDerivAt.comp 0 hDgT
    constructor
    · simp only [rho,Q,inner_zero_right,zero_smul,sub_zero,hgp0]
    · rw [hDrho.fderiv]
      ext y
      exact hlT y
  · have hmap : Tendsto (fun q : P × E => (q.1,Q q)) (𝓝 (s,0)) (𝓝 (s,0)) := by
      have hh := (contDiffAt_fst.prodMk hQ).continuousAt
      change Tendsto (fun q : P × E => (q.1,Q q)) (𝓝 (s,0)) (𝓝 (s,Q (s,0))) at hh
      simpa only [hQ0] using hh
    filter_upwards [hmap.eventually hright] with q hq
    intro hqN
    let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (N q.1)
    have hl (y : E) : l y=inner ℝ (N q.1) y := rfl
    have hlN : l (N q.1)=1 := by
      change inner ℝ (N q.1) (N q.1)=1
      rw [real_inner_self_eq_norm_sq,hqN]
      norm_num
    have hlQ : l (Q q)=0 := by
      change l (q.2-l q.2 • N q.1)=0
      rw [map_sub,map_smul,hlN,smul_eq_mul,mul_one,sub_self]
    have hlF (y : E) : l (F (q.1,y))=f (q.1,y) := by
      change l (y+(f (q.1,y)-l y) • N q.1)=f (q.1,y)
      rw [map_add,map_smul,hlN,smul_eq_mul,mul_one]
      ring
    have hfzero : f (q.1,g (q.1,Q q))=0 := by rw [← hlF,hq,hlQ]
    have he : g (q.1,Q q)=Q q+rho q • N q.1 := by
      change g (q.1,Q q)+(f (q.1,g (q.1,Q q))-l (g (q.1,Q q))) • N q.1=Q q at hq
      rw [hfzero,zero_sub,neg_smul] at hq
      have hh : g (q.1,Q q)-rho q • N q.1=Q q := by
        simpa only [rho,sub_eq_add_neg,hl] using hq
      exact sub_eq_iff_eq_add.mp hh
    change f (q.1,Q q+rho q • N q.1)=0
    rw [← he]
    exact hfzero

end PowerConvexity
