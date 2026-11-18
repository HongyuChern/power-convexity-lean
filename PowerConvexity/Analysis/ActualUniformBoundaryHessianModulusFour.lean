import PowerConvexity.Analysis.ActualDomainClosureC2JetFour

/-! # A common boundary Hessian modulus from common actual expansions

The constants below precede the choice of the solution and its expansion.
Only the uniform expansion remains an input.  In particular, continuity of
each individual closure jet is never used to assert equicontinuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_domain_extension_boundary_holder_four
    {Z : Type*} [NormedAddCommGroup Z]
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {f g : E → Z} {C K epsilon radius gamma : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hg : 0 ≤ gamma)
    (herr : ∀ x ∈ U, infDist x (frontier U) < epsilon →
      ‖f x-g (actualBoundaryFootOnDomainFour U hproper x)‖ ≤
        C*(infDist x (frontier U))^gamma)
    (hboundary : ∀ c ∈ frontier U, ∀ d ∈ frontier U,
      ‖c-d‖ < radius → ‖g c-g d‖ ≤ K*‖c-d‖^gamma)
    {c x : E} (hc : c ∈ frontier U) (hx : x ∈ closure U)
    (hnear : ‖x-c‖ < min epsilon (radius/2)) :
    ‖actualDomainJetExtensionFour U f g x-g c‖ ≤
      (C+K*(2 : ℝ)^gamma)*‖x-c‖^gamma := by
  let p := actualBoundaryFootOnDomainFour U hproper x
  have hp : p ∈ frontier U := (actual_boundary_foot_mem_dist_four hU hproper hx).1
  have hdist : infDist x (frontier U) ≤ ‖x-c‖ := by
    simpa only [dist_eq_norm] using infDist_le_dist_of_mem hc (x := x)
  have hpc : ‖p-c‖ ≤ 2*‖x-c‖ := by
    simpa only [dist_eq_norm] using actual_boundary_foot_distance_four hU hproper hx hc
  have hpnear : ‖p-c‖ < radius := by
    have hh := hnear.trans_le (min_le_right _ _)
    linarith
  have hgp : ‖g p-g c‖ ≤ K*(2*‖x-c‖)^gamma :=
    (hboundary p hp c hc hpnear).trans (by gcongr)
  have he : ‖actualDomainJetExtensionFour U f g x-g p‖ ≤ C*‖x-c‖^gamma := by
    by_cases hxi : x ∈ U
    · rw [actualDomainJetExtensionFour,if_pos hxi]
      exact (herr x hxi (hdist.trans_lt (hnear.trans_le (min_le_left _ _)))).trans
        (by gcongr; exact infDist_nonneg)
    · have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx,hxi⟩
      have hpx : p=x := actual_boundary_foot_fixed_four hU hproper hxf
      rw [actualDomainJetExtensionFour,if_neg hxi,hpx,sub_self,norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
  have htri : ‖actualDomainJetExtensionFour U f g x-g c‖ ≤
      ‖actualDomainJetExtensionFour U f g x-g p‖+‖g p-g c‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (actualDomainJetExtensionFour U f g x) (g p) (g c)
  apply (htri.trans (add_le_add he hgp)).trans_eq
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
  ring

theorem actual_uniform_boundary_hessian_modulus_of_expansion_four
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter R gamma M T lam Lambda alpha Ka Kf : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hball : closedBall o rho ⊆ U)
    (hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter) :
    ∃ K ≥ 0, ∃ delta > 0,
      ∀ D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf,
      ∀ J : ActualDomainBoundaryExpansionFour D R gamma M T,
      ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
        ‖actualDomainJetExtensionFour U (realHessian D.solution)
          (fun y => realHessian (J.polynomial y) y) x-realHessian (J.polynomial c) c‖ ≤
          K*‖x-c‖^gamma := by
  obtain ⟨C,hC,hcontrol⟩ := actual_domain_boundary_interior_jet_control_four
    hlam hLambda halpha hg hga hKa hKf hM hT
  let B := 256*M*(diameter+rho)^2/rho^2*(4 : ℝ)^gamma
  let epsilon := min 1 (R/2)
  let radius := min (R/4) (diameter+rho)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he : 0 < epsilon := lt_min zero_lt_one (half_pos hR)
  have hr : 0 < radius := by dsimp [radius]; positivity
  refine ⟨C+B*(2 : ℝ)^gamma,by positivity,min epsilon (radius/2),
    lt_min he (half_pos hr),?_⟩
  intro D J c hc x hx hnear
  apply actual_domain_extension_boundary_holder_four hU hproper hC hB hg.le
    (f := realHessian D.solution) (g := fun y => realHessian (J.polynomial y) y)
    (epsilon := epsilon) (radius := radius) ?_ ?_ hc hx hnear
  · intro y hy hye
    have hh := (hcontrol U hU hproper D R hR J y hy hye).2
    apply hh.trans
    have hd : 0 ≤ infDist y (frontier U) := infDist_nonneg
    have hle : infDist y (frontier U)/4 ≤ infDist y (frontier U) := by linarith
    gcongr
  · intro p hp q hq hpq
    exact actual_convex_boundary_hessian_holder_four hU hconv hrho hdia hR hM hg.le
      hball frontier_subset_closure hbound J.quadratic J.remainder p hp q hq hpq

theorem actual_domain_closure_hessian_eq_expansion_four
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter R gamma M T lam Lambda alpha Ka Kf : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hball : closedBall o rho ⊆ U)
    (hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    (D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (J : ActualDomainBoundaryExpansionFour D R gamma M T)
    (J0 : ClosureC2Jet D.solution U) :
    EqOn J0.hessian (actualDomainJetExtensionFour U (realHessian D.solution)
      (fun y => realHessian (J.polynomial y) y)) (closure U) := by
  obtain ⟨C,hC,hcontrol⟩ := actual_domain_boundary_interior_jet_control_four
    hlam hLambda halpha hg hga hKa hKf hM hT
  have hhfield := (actual_domain_boundary_polynomial_jets_continuous_four
    hU hconv hrho hdia hR hg hM hball hbound D J).2
  have hd : ContDiffOn ℝ 1 (fderiv ℝ D.solution) U :=
    D.solution_regular.fderiv_of_isOpen hU (by norm_num)
  have hHc : ContinuousOn (realHessian D.solution) U :=
    hd.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hext : ContinuousOn (actualDomainJetExtensionFour U (realHessian D.solution)
      (fun y => realHessian (J.polynomial y) y)) (closure U) := by
    have hw : Continuous (fun s : ℝ => C*(s/4)^gamma) :=
      continuous_const.mul ((Real.continuous_rpow_const hg.le).comp (continuous_id.div_const 4))
    apply actual_domain_jet_extension_continuous_four hU hproper hHc hhfield
      (lt_min zero_lt_one (half_pos hR)) (w := fun s : ℝ => C*(s/4)^gamma)
      hw.continuousAt (by simp only [zero_div,Real.zero_rpow hg.ne',mul_zero])
    intro x hx hnear
    exact (hcontrol U hU hproper D R hR J x hx hnear).2
  have he : EqOn J0.hessian (actualDomainJetExtensionFour U (realHessian D.solution)
      (fun y => realHessian (J.polynomial y) y)) U := by
    intro x hx
    rw [actualDomainJetExtensionFour,if_pos hx]
    exact J0.hessian_eq hx
  exact he.of_subset_closure J0.continuous_hessian hext subset_closure Subset.rfl

theorem actual_uniform_closureJet_boundary_hessian_modulus_four
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter R gamma M T lam Lambda alpha Ka Kf : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hball : closedBall o rho ⊆ U)
    (hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter) :
    ∃ K ≥ 0, ∃ delta > 0,
      ∀ D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf,
      ∀ J : ActualDomainBoundaryExpansionFour D R gamma M T,
      ∀ J0 : ClosureC2Jet D.solution U,
      ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
        ‖J0.hessian x-J0.hessian c‖ ≤ K*‖x-c‖^gamma := by
  obtain ⟨K,hK,delta,hdelta,hmod⟩ := actual_uniform_boundary_hessian_modulus_of_expansion_four
    hU hproper hconv hrho hdia hR hlam hLambda halpha hg hga hKa hKf hM hT hball hbound
  refine ⟨K,hK,delta,hdelta,?_⟩
  intro D J J0 c hc x hx hnear
  have he := actual_domain_closure_hessian_eq_expansion_four hU hproper hconv
    hrho hdia hR hlam hLambda halpha hg hga hKa hKf hM hT hball hbound D J J0
  rw [he hx,he (frontier_subset_closure hc)]
  have hcn : c ∉ U := by rw [hU.frontier_eq] at hc; exact hc.2
  simpa only [actualDomainJetExtensionFour,if_neg hcn] using hmod D J c hc x hx hnear

end PowerConvexity
