import PowerConvexity.Analysis.ActualUniformMixedBoundaryDecayFour
import PowerConvexity.Analysis.ActualUniformBoundaryNormalRecoveryTwo

/-! # A true common nonlinear Hessian modulus at the nearest boundary point

All constants precede the genuine nonlinear solution and its actual closure
jet. The proof uses its rough tangential equations, the radius-uniform interior
estimate, the true zero trace and the same determinant. No coefficient or
boundary Hessian modulus occurs among the hypotheses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_nonlinear_nearest_boundary_hessian_modulus_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hproper : U≠univ) {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hgb : ∀ c ∈ frontier U, g c=0 ∧ fderiv ℝ g c≠0)
    (hgdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {G H P F D Csrc : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hF : 0 ≤ F) (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ ∃ C ≥ 0,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 2 rho U →
      ContinuousOn rho (closure U) → ∀ J : ClosureC2Jet u U,
      (∀ x ∈ frontier U, u x=0) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x ∧ rho x ≤ D) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure U, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ U, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      ∀ x ∈ U, infDist x (frontier U) < R →
        ‖realHessian u x-J.hessian (actualBoundaryFootOnDomainFour U hproper x)‖ ≤
          C*(infDist x (frontier U))^gamma := by
  obtain ⟨R,hR,hR1,gamma,hgamma,hgamma1,C,hC,hmixed⟩ :=
    actual_uniform_mixed_nearest_boundary_decay_four hU hconv hK hproper hg hgb hgdef
      hG hH hP hF hD hCsrc hg1 hg2 hg3
  let A := 3*C+4*(P+3*H*C)*(H+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨R,hR,hR1,gamma,hgamma,hgamma1,A,hA,?_⟩
  intro u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource x hx hxR
  let c := actualBoundaryFootOnDomainFour U hproper x
  let d := infDist x (frontier U)
  have hd : 0 < d := (actual_boundary_distance_ball_four hU hproper hx).1
  have hd1 : d ≤ 1 := hxR.le.trans hR1
  have hfoot := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
  have hc : c ∈ frontier U := hfoot.1
  have hcC : c ∈ closure U := frontier_subset_closure hc
  have hxc : ‖x-c‖=d := by simpa only [dist_eq_norm] using hfoot.2
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hHu : ‖realHessian u x‖ ≤ H := by
    change ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H
    rw [← J.hessian_eq hx]
    exact hJH x (subset_closure hx)
  have hrhoLip (z : E) (hz : z ∈ U) : |rho x-rho z| ≤ P*‖x-z‖ := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => ((hrho.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)))
      hrhoD hconv hz hx
  have hdelta : |rho x-rho c| ≤ P*d := by
    rw [← hxc]
    exact le_on_closure hrhoLip (continuousOn_const.sub hrhoC).abs
      (show ContinuousOn (fun z : E => P*‖x-z‖) (closure U) by fun_prop) hcC
  let N := actualDefiningUnitNormalFour g c
  obtain ⟨hN,_,hDcov⟩ := actual_defining_unit_normal_four (hgb c hc).2
  have hmix : ∀ w : E, inner ℝ N w=0 →
      ‖(realHessian u x-J.hessian c).flip w‖ ≤ (C*d^gamma)*‖w‖ := by
    intro w hw
    apply hmixed u rho hu hrho J hzero hpos hdet hrhob hJu hJH hrhoD hsource x hx hxR w
    rw [hDcov]
    change ‖fderiv ℝ g c‖*inner ℝ N w=0
    rw [hw,mul_zero]
  have hh := actual_boundary_full_hessian_from_mixed_two hU hu2 J hrhoC hpos hdet
    (fun z hz => (hrhob z hz).1) hx hcC hN hH (show 0 ≤ C*d^gamma by positivity)
    hHu (hJH c hcC) hmix hdelta
  have hdPower : d ≤ d^gamma := Real.self_le_rpow_of_le_one hd.le hd1 hgamma1.le
  change ‖realHessian u x-J.hessian c‖ ≤ A*d^gamma
  calc
    _ ≤ 3*(C*d^gamma)+4*(P*d+3*H*(C*d^gamma))*(H+1) := hh
    _ ≤ 3*(C*d^gamma)+4*(P*d^gamma+3*H*(C*d^gamma))*(H+1) := by
      gcongr
    _ = A*d^gamma := by dsimp only [A]; ring

end PowerConvexity
