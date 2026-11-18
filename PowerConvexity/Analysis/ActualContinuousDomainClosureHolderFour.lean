import PowerConvexity.Analysis.ActualContinuousDomainGlobalHolderFour
import PowerConvexity.Analysis.ActualContinuousDomainClosureC2JetFour

/-! # Global actual closure C2 Holder jets from the same boundary expansions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_holder_bound_on_closure_four {Z : Type*} [NormedAddCommGroup Z]
    {U : Set E} {f : E → Z} (hf : ContinuousOn f (closure U))
    {C alpha : ℝ} (halpha : 0 ≤ alpha)
    (hb : ∀ x ∈ U, ∀ y ∈ U, ‖f x-f y‖ ≤ C*‖x-y‖^alpha) :
    ∀ x ∈ closure U, ∀ y ∈ closure U, ‖f x-f y‖ ≤ C*‖x-y‖^alpha := by
  have hone : ∀ x ∈ closure U, ∀ y ∈ U, ‖f x-f y‖ ≤ C*‖x-y‖^alpha := by
    intro x hx y hy
    apply le_on_closure (fun z hz => hb z hz y hy)
      ((hf.sub continuousOn_const).norm) _ hx
    exact (continuous_const.mul ((Real.continuous_rpow_const halpha).comp
      ((continuous_id.sub continuous_const).norm))).continuousOn
  intro x hx y hy
  apply le_on_closure (fun z hz => hone x hx z hz)
    ((continuousOn_const.sub hf).norm) _ hy
  exact (continuous_const.mul ((Real.continuous_rpow_const halpha).comp
    ((continuous_const.sub continuous_id).norm))).continuousOn

theorem actual_continuous_domain_global_closure_holder_four
    {rho diameter R lam Lambda alpha Ka Kf F B M T G : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hG : 0 ≤ G) :
    ∃ C ≥ 0, ∀ U : Set E, ∀ hU : IsOpen U, ∀ hproper : U ≠ univ,
    Convex ℝ U → ∀ o : E, closedBall o rho ⊆ U →
    (∀ c ∈ frontier U, ‖o-c‖ ≤ diameter) →
    ∀ D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf,
    (∀ x ∈ U, |D.source x| ≤ F) → (∀ x ∈ U, |D.solution x| ≤ B) →
    ∀ J : ActualContinuousDomainBoundaryExpansionFour D R M T,
    (∀ c ∈ frontier U, ‖fderiv ℝ (J.polynomial c) c‖ ≤ G) →
    ∃ Jc : ClosureC2Jet D.solution U,
      (∀ x ∈ closure U, |D.solution x| ≤ C ∧ ‖Jc.derivative x‖ ≤ C ∧ ‖Jc.hessian x‖ ≤ C) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U, ‖Jc.hessian x-Jc.hessian y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨C,hC,hglobal⟩ := actual_continuous_domain_global_holder_four hrho hdia hR hlam hLambda
    halpha halpha1 hKa hKf hF hB hM hT hG
  refine ⟨C,hC,?_⟩
  intro U hU hproper hconv o hball hdiam D hfb hub J hGb
  obtain ⟨Jc⟩ := actual_continuous_domain_closure_C2_jet_of_expansion_four hU hproper hconv
    hrho hdia hR hlam hLambda halpha halpha1 hKa hKf hM hT hball hdiam D J
  obtain ⟨hbound,hholder⟩ := hglobal U hU hproper hconv o hball hdiam D hfb hub J hGb
  refine ⟨Jc,?_,?_⟩
  · intro x hx
    refine ⟨?_,?_,?_⟩
    · exact le_on_closure (fun y hy => (hbound y hy).1)
        Jc.continuous_value.abs continuousOn_const hx
    · apply le_on_closure (fun y hy => ?_) Jc.continuous_derivative.norm continuousOn_const hx
      rw [Jc.derivative_eq hy]
      exact (hbound y hy).2.1
    · refine le_on_closure (f := fun y => ‖Jc.hessian y‖) (g := fun _ => C)
        ?_ ?_ continuousOn_const hx
      · intro y hy
        rw [Jc.hessian_eq hy]
        exact (hbound y hy).2.2
      · exact (continuous_norm : Continuous (fun H : E →L[ℝ] E →L[ℝ] ℝ => ‖H‖)).comp_continuousOn
          Jc.continuous_hessian
  · apply actual_holder_bound_on_closure_four (Z := E →L[ℝ] E →L[ℝ] ℝ)
      (U := U) (f := Jc.hessian) Jc.continuous_hessian halpha.le
    intro x hx y hy
    rw [Jc.hessian_eq hx,Jc.hessian_eq hy]
    exact hholder x hx y hy

end PowerConvexity
