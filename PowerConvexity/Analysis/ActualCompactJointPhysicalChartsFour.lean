import PowerConvexity.Analysis.ActualCompactJointNormalizedDefiningGraphs
import PowerConvexity.Analysis.ActualCommonChartRoughBoundaryExpansionFour

/-! # Actual physical charts uniform on a compact moving boundary graph

Joint regular defining geometry produces one physical scale and one graph
bound for every fiber. Orthogonal normal choices are made pointwise; their
continuity is neither assumed nor used. All domain-side equivalences remain
those of the actual moving domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_compact_covector_fixed_normal_four
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    {D : P → E →L[ℝ] ℝ} (hD : ContinuousOn D K) (hDn : ∀ p ∈ K, D p≠0)
    {N : E} (hN : ‖N‖=1) :
    ∃ Z > 0, ∀ p ∈ K, ∃ G : E ≃L[ℝ] E,
      ‖G.toContinuousLinearMap‖ ≤ 1 ∧ ‖G.symm.toContinuousLinearMap‖ ≤ 1 ∧
      ∃ zeta : ℝ, zeta<0 ∧ |zeta| ≤ Z ∧
        ∀ v : E, zeta*D p (G v)=inner ℝ N v := by
  have hc : ContinuousOn (fun p => (‖D p‖)⁻¹) K :=
    hD.norm.inv₀ (fun p hp => norm_ne_zero_iff.mpr (hDn p hp))
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨|B|+1,by positivity,?_⟩
  intro p hp
  let V : E := -((InnerProductSpace.toDual ℝ E).symm (D p))
  have hVnorm : ‖V‖=‖D p‖ := by
    rw [norm_neg]
    exact (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hn : 0 < ‖D p‖ := norm_pos_iff.mpr (hDn p hp)
  have hV : V≠0 := norm_ne_zero_iff.mp (by rw [hVnorm]; exact hn.ne')
  obtain ⟨O,hO⟩ := actual_normal_alignment_four hN hV
  have hOb : ‖O.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    simpa only [ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      O.norm_map,one_mul] using le_refl ‖v‖
  have hOib : ‖O.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change ‖O.symm v‖ ≤ 1*‖v‖
    rw [O.symm.norm_map,one_mul]
  refine ⟨O.toContinuousLinearEquiv,hOb,hOib,-(‖D p‖)⁻¹,
    neg_neg_of_pos (inv_pos.mpr hn),?_,?_⟩
  · rw [abs_neg,abs_of_pos (inv_pos.mpr hn)]
    have hh := hB _ (mem_image_of_mem _ hp)
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)] at hh
    exact hh.trans (by linarith [le_abs_self B])
  · intro v
    have hh := hO v
    rw [hVnorm] at hh
    have hv : inner ℝ V (O v)=-(D p (O v)) := by
      simp only [V,inner_neg_left,InnerProductSpace.toDual_symm_apply]
    rw [hv] at hh
    change -(‖D p‖)⁻¹*D p (O v)=inner ℝ N v
    field_simp
    nlinarith

theorem actual_compact_joint_unit_boundary_charts_four
    {V : ℝ → Set E} {S : Set ℝ} {K : Set (ℝ × E)} (hK : IsCompact K)
    (hgraph : ∀ t ∈ S, ∀ c ∈ frontier (V t), (t,c) ∈ K)
    {f : ℝ × E → ℝ} (hf : ∀ p ∈ K, ContDiffAt ℝ 3 f p)
    (hf0 : ∀ p ∈ K, f p=0)
    (hDf : ∀ p ∈ K, fderiv ℝ (fun y => f (p.1,y)) p.2≠0)
    (hside : ∀ p ∈ K, ∀ᶠ q in 𝓝 p,
      q.1 ∈ S → (q.2 ∈ V q.1 ↔ f q<0)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ H > 0,
      ∀ t ∈ S, ActualUnitBoundaryChartsFour (V t) r H := by
  let N : E := EuclideanSpace.single 0 1
  have hN : ‖N‖=1 := by simp only [N,EuclideanSpace.norm_single,norm_one]
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fun y => f (p.1,y)) p.2) K := by
    intro p hp
    exact (parameter_fiber_fderiv_contDiffAt (n := 2) (hf p hp)).continuousAt.continuousWithinAt
  obtain ⟨Z,hZ,hnormal⟩ := actual_compact_covector_fixed_normal_four hK hDc hDf hN
  obtain ⟨R,hR,hR1,M,hM,hgraphs⟩ := actual_compact_joint_normalized_defining_graphs
    hK hf hf0 1 Z
  let Q : Set (ℝ × E) := {q | q.1 ∈ S → (q.2 ∈ V q.1 ↔ f q<0)}
  have hKQ : K ⊆ interior Q := fun p hp => mem_interior_iff_mem_nhds.mpr (hside p hp)
  obtain ⟨d,hd,hnear⟩ := hK.exists_thickening_subset_open isOpen_interior hKQ
  have hQ (p : ℝ × E) (hp : p ∈ K) (q : ℝ × E) (hq : dist q p<d) : q ∈ Q := by
    apply interior_subset (hnear ?_)
    exact mem_thickening_iff.mpr ⟨p,hp,hq⟩
  let T := min R (d/(2*(1+M)))
  have hT : 0 < T := lt_min hR (div_pos hd (by positivity))
  have hTR : T ≤ R := min_le_left _ _
  have hTd : T ≤ d/(2*(1+M)) := min_le_right _ _
  let r := min (T/4) (min 1 (1/(4*(M+1))))
  have hr : 0 < r := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hrT : r ≤ T/4 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrcap : r ≤ 1/(4*(M+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hr2T : 2*r ≤ T := by linarith
  have hrM : r*M ≤ M := (mul_le_mul_of_nonneg_right hr1 hM.le).trans_eq (one_mul _)
  have hsmall : 2*r*M ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(M+1))).mp hrcap
    nlinarith [mul_nonneg hr.le hM.le]
  refine ⟨r,hr,hr1,M,hM,?_⟩
  intro t ht c hc
  have hp : (t,c) ∈ K := hgraph t ht c hc
  obtain ⟨G,hGB,hGI,zeta,hz,hzZ,hDnorm⟩ := hnormal (t,c) hp
  obtain ⟨rho,hrho0,hD0,hinv,hreg,hsign⟩ :=
    hgraphs (t,c) hp G.toContinuousLinearMap hGB N hN zeta hzZ hDnorm
  have hrhov (x : E) (hx : x ∈ closedBall (0 : E) R) : |rho x| ≤ M*‖x‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hreg y hy).1.differentiableAt (by norm_num))
      (fun y hy => (hreg y hy).2.1) (convex_closedBall (0 : E) R)
      (mem_closedBall_self hR.le) hx
    simpa only [hrho0,sub_zero,Real.norm_eq_abs] using hh
  have hmap (x : E) (hx : x ∈ closedBall (0 : E) T) :
      c+G (actualGraphShearFour N rho x) ∈ V t ↔ 0 < inner ℝ N x := by
    have hxR := closedBall_subset_closedBall hTR hx
    have hxT : ‖x‖ ≤ T := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hShear : ‖actualGraphShearFour N rho x‖ ≤ (1+M)*‖x‖ := by
      calc
        _ ≤ ‖x‖+‖rho x • N‖ := norm_add_le _ _
        _ = ‖x‖+|rho x| := by rw [norm_smul,Real.norm_eq_abs,hN,mul_one]
        _ ≤ ‖x‖+M*‖x‖ := add_le_add (le_refl _) (hrhov x hxR)
        _ = _ := by ring
    have hdist : ‖(c+G (actualGraphShearFour N rho x))-c‖ < d := by
      have hBD : (1+M)*T ≤ d/2 := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2*(1+M))).mp hTd
        nlinarith
      calc
        _ = ‖G (actualGraphShearFour N rho x)‖ := by rw [add_sub_cancel_left]
        _ ≤ 1*‖actualGraphShearFour N rho x‖ :=
          (G.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hGB (norm_nonneg _))
        _ ≤ (1+M)*‖x‖ := by simpa only [one_mul] using hShear
        _ ≤ (1+M)*T := by gcongr
        _ ≤ d/2 := hBD
        _ < d := by linarith
    have hpairdist : dist (t,c+G (actualGraphShearFour N rho x)) (t,c)<d := by
      change max (dist t t) (dist (c+G (actualGraphShearFour N rho x)) c)<d
      rw [dist_self,max_eq_right dist_nonneg]
      simpa only [dist_eq_norm] using hdist
    have hsideX := hQ (t,c) hp (t,c+G (actualGraphShearFour N rho x)) hpairdist ht
    have hsignX := (hsign x hxR).1
    have hmul : (f (t,c+G (actualGraphShearFour N rho x))<0) ↔
        0 < zeta*f (t,c+G (actualGraphShearFour N rho x)) := by
      constructor
      · exact mul_pos_of_neg_of_neg hz
      · intro hpos
        by_contra hn
        exact not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hz.le (le_of_not_gt hn)) hpos
    exact hsideX.trans (hmul.trans hsignX)
  let psi := actualPhysicalGraphHeightFour rho r
  have hj := actual_physical_graph_regularity_four
    (hreg 0 (mem_closedBall_self hR.le)).1 hrho0 hD0 (R := r)
  have hbds := actual_physical_graph_uniform_derivative_bounds_four hT hr hr2T hM.le
    (fun x hx => (hreg x (closedBall_subset_closedBall hTR hx)).1) hD0
    (fun x hx => (hreg x (closedBall_subset_closedBall hTR hx)).2.2.1)
    (fun x hx => (hreg x (closedBall_subset_closedBall hTR hx)).2.2.2)
  refine ⟨G,hGB,hGI,psi,hj.2.1,hj.2.2,
    actual_physical_graph_normal_invariance_four hinv r,?_,?_⟩
  · intro x hx
    exact ⟨(hbds.1 x hx).1,((hbds.1 x hx).2.1).trans hsmall,((hbds.1 x hx).2.2).trans hrM⟩
  · intro x hx
    have hx2 : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hscale : r • x ∈ closedBall (0 : E) T := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hx2 hr.le).trans (by linarith)
    rw [actual_physical_graph_conjugation_four hr.ne']
    exact (hmap _ hscale).trans (by rw [inner_smul_right]; exact mul_pos_iff_of_pos_left hr)

end PowerConvexity
