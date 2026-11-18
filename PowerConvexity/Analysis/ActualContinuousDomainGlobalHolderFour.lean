import PowerConvexity.Analysis.ActualContinuousDomainInteriorHolderFour
import PowerConvexity.Analysis.ActualBoundaryScaleHolderGluingFour

/-! # Global actual Schauder control from uniform original-domain boundary expansions

The common boundary radius, expansion constant, polynomial gradient/Hessian
bounds, and the actual coefficient/source Holder bounds stay explicit. The
conclusion has the same exponent throughout the entire original domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuous_domain_global_holder_four
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
    (∀ x ∈ U, |D.solution x| ≤ C ∧ ‖fderiv ℝ D.solution x‖ ≤ C ∧ ‖realHessian D.solution x‖ ≤ C) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      ‖realHessian D.solution x-realHessian D.solution y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨db,hdb,hdb8,Cb,hCb,hboundary⟩ := actual_continuous_domain_boundary_local_holder_four
    hlam hLambda halpha halpha1 hKa hKf hM hT
  let sigma := min 1 (R/2)
  have hsigma : 0 < sigma := lt_min zero_lt_one (half_pos hR)
  let ri := sigma/8
  have hri : 0 < ri := by dsimp [ri]; positivity
  obtain ⟨di,hdi,hdi4,Ci,hCi,hinterior⟩ := actual_continuous_domain_interior_holder_four hri
    hlam hLambda halpha halpha1 hKa hKf hF hB
  let rB := min (R/4) (diameter+rho)
  have hrB : 0 < rB := lt_min (by positivity) (by positivity)
  let Kb := 256*M*(diameter+rho)^2/rho^2*(4 : ℝ)^alpha
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  let Jbound := B+Ci+Cb+5*T+G
  have hJbound : 0 ≤ Jbound := by dsimp [Jbound]; positivity
  obtain ⟨H,hH,hglue⟩ := actual_boundary_scale_holder_gluing_four halpha.le hsigma hrB
    (by positivity : 0 < db/4) hdi hJbound hCb hKb hCb hCi
  let C := Jbound+H
  have hC : 0 ≤ C := add_nonneg hJbound hH
  refine ⟨C,hC,?_⟩
  intro U hU hproper hconv o hball hdiam D hfb hub J hGb
  have hdeepball (x : E) (hx : x ∈ U) (hd : sigma/2 ≤ infDist x (frontier U)) :
      closedBall x (2*ri) ⊆ U := by
    intro y hy
    apply ball_infDist_compl_subset
    rw [mem_ball,← infDist_frontier_eq_compl_of_mem hU hproper hx]
    have hdist : dist y x ≤ 2*ri := hy
    dsimp [ri] at hdist
    linarith
  have hnorms : ∀ x ∈ U,
      |D.solution x| ≤ Jbound ∧ ‖fderiv ℝ D.solution x‖ ≤ Jbound ∧ ‖realHessian D.solution x‖ ≤ Jbound := by
    intro x hx
    have hvalue : |D.solution x| ≤ Jbound := (hub x hx).trans (by dsimp [Jbound]; linarith)
    by_cases hnear : infDist x (frontier U) < sigma
    · let c := actualBoundaryFootOnDomainFour U hproper x
      let r := infDist x (frontier U)/4
      have hcontrol := hboundary U hU hproper D R hR J x hx hnear
      have hc : c ∈ frontier U := (actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)).1
      have hr0 : 0 ≤ r := div_nonneg infDist_nonneg (by norm_num)
      have hr1 : r ≤ 1 := by
        have hh : infDist x (frontier U) < 1 := hnear.trans_le (min_le_left _ _)
        dsimp [r]; linarith
      have hrpow : r^alpha ≤ 1 := Real.rpow_le_one hr0 hr1 halpha.le
      have hqb : ‖realHessian (J.polynomial c) c‖ ≤ T := by
        rw [quadratic_realHessian_from_jet_zero (J.quadratic c hc) c]
        exact J.hessian_bound c hc
      have hgrad : ‖fderiv ℝ D.solution x‖ ≤ Cb+4*T+G := by
        calc
          _ = ‖(fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c)+fderiv ℝ (J.polynomial c) c‖ := by rw [sub_add_cancel]
          _ ≤ ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖+‖fderiv ℝ (J.polynomial c) c‖ := norm_add_le _ _
          _ ≤ (Cb+4*T)*r+G := add_le_add hcontrol.1 (hGb c hc)
          _ ≤ Cb+4*T+G := by nlinarith [mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ Cb+4*T)]
      have hhess : ‖realHessian D.solution x‖ ≤ Cb+T := by
        calc
          _ = ‖(realHessian D.solution x-realHessian (J.polynomial c) c)+realHessian (J.polynomial c) c‖ := by
            congr 1
            ext v w
            simp only [_root_.sub_apply,_root_.add_apply]
            ring
          _ ≤ ‖realHessian D.solution x-realHessian (J.polynomial c) c‖+‖realHessian (J.polynomial c) c‖ :=
            norm_add_le (realHessian D.solution x-realHessian (J.polynomial c) c) (realHessian (J.polynomial c) c)
          _ ≤ Cb*r^alpha+T := add_le_add hcontrol.2.1 hqb
          _ ≤ Cb+T := by nlinarith [mul_le_mul_of_nonneg_left hrpow hCb]
      exact ⟨hvalue,hgrad.trans (by dsimp [Jbound]; linarith),hhess.trans (by dsimp [Jbound]; linarith)⟩
    · have hdeep : sigma/2 ≤ infDist x (frontier U) := by linarith [le_of_not_gt hnear]
      have hi := (hinterior U hU D hfb hub x (hdeepball x hx hdeep)).1
      exact ⟨hvalue,hi.2.1.trans (by dsimp [Jbound]; linarith),hi.2.2.trans (by dsimp [Jbound]; linarith)⟩
  have hholder : ∀ x ∈ U, ∀ y ∈ U,
      ‖realHessian D.solution x-realHessian D.solution y‖ ≤ H*‖x-y‖^alpha := by
    have hh := hglue (E →L[ℝ] E →L[ℝ] ℝ) U hU hproper
      (realHessian D.solution) (fun c => realHessian (J.polynomial c) c)
      (fun x hx => (hnorms x hx).2.2) ?_ ?_ ?_ ?_
    · intro x hx y hy
      simpa only [dist_eq_norm] using hh x hx y hy
    · intro c hc d hd hnear
      simpa only [dist_eq_norm,Kb,rB] using actual_convex_boundary_hessian_holder_four hU hconv
        hrho hdia hR hM halpha.le hball frontier_subset_closure hdiam J.quadratic J.remainder c hc d hd
        (by simpa only [dist_eq_norm,rB] using hnear)
    · intro x hx hnear
      have hc := (hboundary U hU hproper D R hR J x hx hnear).2.1
      have hpow : (infDist x (frontier U)/4)^alpha ≤ (infDist x (frontier U))^alpha :=
        Real.rpow_le_rpow (div_nonneg infDist_nonneg (by norm_num)) (by nlinarith [infDist_nonneg (x := x) (s := frontier U)]) halpha.le
      have hhc : dist (realHessian D.solution x)
          (realHessian (J.polynomial (actualBoundaryFootOnDomainFour U hproper x))
            (actualBoundaryFootOnDomainFour U hproper x)) ≤ Cb*(infDist x (frontier U)/4)^alpha := by
        rw [dist_eq_norm (realHessian D.solution x)
          (realHessian (J.polynomial (actualBoundaryFootOnDomainFour U hproper x))
            (actualBoundaryFootOnDomainFour U hproper x))]
        exact hc
      exact hhc.trans (mul_le_mul_of_nonneg_left hpow hCb)
    · intro x hx hnear y hy hxy
      have he : ‖x-y‖ < (infDist x (frontier U)/4)*db := by
        have hh : ‖x-y‖ < (db/4)*infDist x (frontier U) := by simpa only [dist_eq_norm] using hxy
        nlinarith
      simpa only [dist_eq_norm] using (hboundary U hU hproper D R hR J x hx hnear).2.2 y hy he
    · intro x hx hdeep y hy hxy
      have he : y ∈ ball x di := by simpa only [mem_ball,dist_comm] using hxy
      simpa only [dist_eq_norm] using (hinterior U hU D hfb hub x (hdeepball x hx hdeep)).2 y he
  constructor
  · intro x hx
    have hbound : Jbound ≤ C := by dsimp [C]; linarith
    exact ⟨(hnorms x hx).1.trans hbound,(hnorms x hx).2.1.trans hbound,(hnorms x hx).2.2.trans hbound⟩
  · intro x hx y hy
    exact (hholder x hx y hy).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : H ≤ C) (Real.rpow_nonneg (norm_nonneg _) _))

end PowerConvexity
