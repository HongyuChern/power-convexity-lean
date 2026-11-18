import PowerConvexity.Analysis.ActualCommonTangentialBoundaryDecayFour
import PowerConvexity.Analysis.ActualUniformMixedBoundaryDecayFour

/-! # Common mixed Hessian decay before all actual domains

The displayed common defining-normal margin identifies the actual mixed
Hessian covectors. Neither a solution's boundary modulus nor a third-jet
bound is among the inputs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_common_mixed_nearest_boundary_decay_four
    {r Hchart F delta rho0 Dout G H P D Csrc : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc) :
    ∃ R > 0, R ≤ 1 ∧ ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ContDiffOn ℝ 2 rho Geo.domain →
      ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ Geo.domain, 1 ≤ rho x ∧ rho x ≤ D) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ Geo.domain, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ Geo.domain, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      ∀ x ∈ Geo.domain, infDist x (frontier Geo.domain) < R →
      let c := actualBoundaryFootOnDomainFour Geo.domain Geo.proper x
      ∀ w : E, fderiv ℝ Geo.defining c w=0 →
        ‖(realHessian u x-J.hessian c).flip w‖ ≤ C*(infDist x (frontier Geo.domain))^gamma*‖w‖ := by
  obtain ⟨R,hR,hR1,gamma,hgamma,hgamma1,C,hC,hdecay⟩ :=
    actual_common_tangential_nearest_boundary_decay_four
      (delta := delta) (rho0 := rho0) (Dout := Dout) hr hr1 hHchart hG hH hP hF hD hCsrc
  let A := 2*H*(2*F)+G*(2*F)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let K := (C+A)/delta
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨R,hR,hR1,gamma,hgamma,hgamma1,K,hK0,?_⟩
  intro Geo u rho hu hrho J hzero hpos hdet hrhob hJu hJH hrhoD hsource x hx hxR
  let U := Geo.domain
  let g := Geo.defining
  have hU : IsOpen U := Geo.isOpen
  have hconv : Convex ℝ U := Geo.convex
  have hproper : U≠univ := Geo.proper
  have hg : ContDiff ℝ 3 g := Geo.regular
  have hgb := Geo.boundary
  have hgdef := Geo.side
  have hg1 := Geo.firstBound
  have hg2 := Geo.secondBound
  have hg3 := Geo.thirdBound
  have hmargin := Geo.normalMargin
  let c := actualBoundaryFootOnDomainFour U hproper x
  let d := infDist x (frontier U)
  have hd : 0 < d := (actual_boundary_distance_ball_four hU hproper hx).1
  have hd1 : d ≤ 1 := hxR.le.trans hR1
  have hfoot := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
  have hc : c ∈ frontier U := hfoot.1
  have hcC : c ∈ closure U := frontier_subset_closure hc
  have hxc : ‖x-c‖=d := by simpa only [dist_eq_norm] using hfoot.2
  have huH : ∀ z ∈ U, ‖realHessian u z‖ ≤ H := by
    intro z hz
    change ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ H
    rw [← J.hessian_eq hz]
    exact hJH z (subset_closure hz)
  have huD : ‖fderiv ℝ u x‖ ≤ G := by rw [← J.derivative_eq hx]; exact hJu x (subset_closure hx)
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  apply actual_covector_kernel_bound_of_unit_four (realHessian u x-J.hessian c) (fderiv ℝ g c)
    (show 0 ≤ K*d^gamma by positivity)
  intro e he hDe
  let N := actualDefiningUnitNormalFour g c
  obtain ⟨hN,hDN,hDcov⟩ := actual_defining_unit_normal_four (hgb c hc).2
  let T := actualDefiningTangentialFieldFour g e N
  have hTc : T c=‖fderiv ℝ g c‖ • e := by
    dsimp only [T,N]
    rw [actual_defining_tangential_field_value_four,hDN,hDe,zero_smul,sub_zero]
  obtain ⟨hT,hTb⟩ := actual_defining_tangential_uniform_C2_bounds_four hg hg1 hg2 hg3 he hN
  have hfield : ‖T x-T c‖ ≤ (2*F)*d := by
    rw [← hxc]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ((hT.contDiffAt (x := z)).differentiableAt (by norm_num)))
      (fun z hz => (hTb z hz).2.1) hconv.closure hcC (subset_closure hx)
  have hfieldD : ‖fderiv ℝ T x-fderiv ℝ T c‖ ≤ (2*F)*d := by
    rw [← hxc]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (((hT.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      (fun z hz => (hTb z hz).2.2) hconv.closure hcC (subset_closure hx)
  have hJlip : ‖fderiv ℝ u x-J.derivative c‖ ≤ H*d := by
    rw [← J.derivative_eq hx,← hxc]
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => closureJet_derivative_hasFDerivWithinAt hU hconv hu2 J hz)
      hJH hconv.closure hcC (subset_closure hx)
  have hresp := hdecay Geo u rho hu hrho J hzero hpos hdet hrhob hJu huH hrhoD hsource e N he hN x hx hxR
  have hh := actual_mixed_closure_covector_modulus_four (e := e) hU J hx
    (hu2.contDiffAt (hU.mem_nhds hx)) ((hT.contDiffAt (x := x)).differentiableAt (by norm_num))
    hdelta (hmargin c hc) hTc hG hH (show 0 ≤ 2*F by positivity) hd.le
    hresp (huH x hx) huD hfield (hTb c hcC).2.1 hJlip hfieldD
  have hdPower : d ≤ d^gamma := Real.self_le_rpow_of_le_one hd.le hd1 hgamma1.le
  calc
    ‖(realHessian u x-J.hessian c).flip e‖ ≤ (C*d^gamma+A*d)/delta := hh
    _ ≤ (C*d^gamma+A*d^gamma)/delta :=
      div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdPower hA)) hdelta.le
    _ = K*d^gamma := by dsimp only [K]; ring


end PowerConvexity
