import PowerConvexity.Calculus.ActualHolderC2JetIdentificationTwo

/-! # Actual closure jets lift uniquely into the complete C2 Holder space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : Set E) [CompactSpace (closure U)]

theorem actualHolderC2JetSpaceTwo_lift (hU : IsOpen U) (alpha : ℝ)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hu0 : ∀ x ∈ frontier U, u x=0)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ closure U, |u x| ≤ B ∧ ‖J.derivative x‖ ≤ B ∧ ‖J.hessian x‖ ≤ B)
    (hh : ∀ x ∈ closure U, ∀ y ∈ closure U, ‖J.hessian x-J.hessian y‖ ≤ B*‖x-y‖^alpha) :
    ∃! p : actualHolderC2JetSpaceTwo U alpha,
      actualHolderC2JetSpaceTwo_value U alpha p=⟨fun x => u x,J.continuous_value.domRestrict⟩ ∧
      ‖p‖ ≤ B := by
  let f : C(closure U,ℝ) := ⟨fun x => u x,J.continuous_value.domRestrict⟩
  let g : C(closure U,E →L[ℝ] ℝ) := ⟨fun x => J.derivative x,J.continuous_derivative.domRestrict⟩
  let h : C(closure U,E →L[ℝ] E →L[ℝ] ℝ) := ⟨fun x => J.hessian x,J.continuous_hessian.domRestrict⟩
  have hfb : ‖f‖ ≤ B := (ContinuousMap.norm_le f hB).mpr (fun x => by
    simpa only [f,ContinuousMap.coe_mk,Real.norm_eq_abs] using (hb x x.property).1)
  have hgb : ‖g‖ ≤ B := (ContinuousMap.norm_le g hB).mpr (fun x => (hb x x.property).2.1)
  have hhb : ‖h‖ ≤ B := (ContinuousMap.norm_le h hB).mpr (fun x => (hb x x.property).2.2)
  obtain ⟨H,hH,_⟩ := actualHolderLoadSpaceTwo_lift (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha h hB
    (fun x y => by simpa only [h,ContinuousMap.coe_mk,Subtype.dist_eq,dist_eq_norm] using hh x x.property y y.property)
  have hHb : ‖H‖ ≤ B := hH.2.trans (max_le hhb le_rfl)
  have hmem : (f,g,H) ∈ actualHolderC2JetSpaceTwo U alpha := by
    constructor
    · intro x hx
      have he : actualClosureExtensionTwo U f =ᶠ[𝓝 x] u := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact actualClosureExtensionTwo_apply U f (subset_closure hy)
      have hd := ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
      rw [← J.derivative_eq hx] at hd
      have hd' := hd.congr_of_eventuallyEq he
      simpa only [actualClosureExtensionTwo_apply U g (subset_closure hx),g,ContinuousMap.coe_mk] using hd'
    constructor
    · intro x hx
      have he : actualClosureExtensionTwo U g =ᶠ[𝓝 x] fderiv ℝ u := by
        filter_upwards [hU.mem_nhds hx] with y hy
        rw [actualClosureExtensionTwo_apply U g (subset_closure hy)]
        exact J.derivative_eq hy
      have hd := (((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt
      rw [← J.hessian_eq hx] at hd
      have hd' := hd.congr_of_eventuallyEq he
      change HasFDerivAt (actualClosureExtensionTwo U g)
        (actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha H) x) x
      rw [hH.1,actualClosureExtensionTwo_apply U h (subset_closure hx)]
      exact hd'
    · intro x hx
      rw [actualClosureExtensionTwo_apply U f (frontier_subset_closure hx)]
      exact hu0 x hx
  let p : actualHolderC2JetSpaceTwo U alpha := ⟨(f,g,H),hmem⟩
  refine ⟨p,⟨rfl,?_⟩,?_⟩
  · change max ‖f‖ (max ‖g‖ ‖H‖) ≤ B
    exact max_le hfb (max_le hgb hHb)
  · intro q hq
    exact actualHolderC2JetSpaceTwo_value_injective U hU alpha hq.1

end PowerConvexity
