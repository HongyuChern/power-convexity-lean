import PowerConvexity.Analysis.ActualCommonTangentialBoundaryCompatibilityFour
import PowerConvexity.Analysis.ActualUniformBoundaryHessianCompatibilityTwo

/-! # Whole-boundary Hessian compatibility uniform before the actual domain

Common physical charts, a true interior ball, the outer boundary radius
and the actual defining-normal margin yield the boundary-pair estimate
for every solution and every domain carrying those genuine data.
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

theorem actual_common_boundary_hessian_compatibility_two
    {r Hchart F delta rho0 Dout G H P : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ContDiffOn ℝ 1 rho Geo.domain →
      ContinuousOn rho (closure Geo.domain) → ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ Geo.domain, 1 ≤ rho x) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ Geo.domain, ‖fderiv ℝ rho x‖ ≤ P) →
      ∀ x ∈ frontier Geo.domain, ∀ c ∈ frontier Geo.domain, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨R,hR,hR1,alpha,ha,ha1,C,hC,hcompat⟩ :=
    actual_common_tangential_boundary_compatibility_four
      (delta := delta) hr hr1 hHchart hrho0 hDout hG hH hP hF
  let A := 2*H*(2*F)+G*(2*F)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let K := (C+A)/delta
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  let B := 3*K+4*(P+3*H*K)*(H+1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨R,hR,hR1,alpha,ha,ha1,B,hB,?_⟩
  intro Geo u rho hu hrho hrhoC J hzero hpos hdet hrho1 hJu hJH hrhoD x hx c hc hnear
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
  have hxC := frontier_subset_closure hx
  have hcC := frontier_subset_closure hc
  let d := ‖x-c‖
  have hd : 0 ≤ d := norm_nonneg _
  have hd1 : d ≤ 1 := hnear.le.trans hR1
  have hdPower : d ≤ d^alpha := Real.self_le_rpow_of_le_one hd hd1 ha1.le
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have huH : ∀ z ∈ U, ‖realHessian u z‖ ≤ H := by
    intro z hz
    change ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ H
    rw [← J.hessian_eq hz]
    exact hJH z (subset_closure hz)
  have hJlip : ‖J.derivative x-J.derivative c‖ ≤ H*d :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => closureJet_derivative_hasFDerivWithinAt hU hconv hu2 J hz)
      hJH hconv.closure hcC hxC
  let N := actualDefiningUnitNormalFour g c
  obtain ⟨hN,hDN,hDcov⟩ := actual_defining_unit_normal_four (hgb c hc).2
  have hmixD : ∀ w : E, fderiv ℝ g c w=0 →
      ‖(J.hessian x-J.hessian c).flip w‖ ≤ (K*d^alpha)*‖w‖ := by
    apply actual_covector_kernel_bound_of_unit_four (J.hessian x-J.hessian c) (fderiv ℝ g c)
      (show 0 ≤ K*d^alpha by positivity)
    intro e he hDe
    let T := actualDefiningTangentialFieldFour g e N
    have hTc : T c=‖fderiv ℝ g c‖ • e := by
      dsimp only [T,N]
      rw [actual_defining_tangential_field_value_four,hDN,hDe,zero_smul,sub_zero]
    obtain ⟨hT,hTb⟩ := actual_defining_tangential_uniform_C2_bounds_four hg hg1 hg2 hg3 he hN
    have hfield : ‖T x-T c‖ ≤ (2*F)*d :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => ((hT.contDiffAt (x := z)).differentiableAt (by norm_num)))
        (fun z hz => (hTb z hz).2.1) hconv.closure hcC hxC
    have hfieldD : ‖fderiv ℝ T x-fderiv ℝ T c‖ ≤ (2*F)*d :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (((hT.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
        (fun z hz => (hTb z hz).2.2) hconv.closure hcC hxC
    have hresp := hcompat Geo u rho hu hrho J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN x hx c hc hnear
    have hh := actual_closure_pair_mixed_covector_modulus_four (e := e) J
      hdelta (hmargin c hc) hTc hG hH (show 0 ≤ 2*F by positivity) hd
      hresp (hJH x hxC) (hJu x hxC) hfield (hTb c hcC).2.1 hJlip hfieldD
    calc
      ‖(J.hessian x-J.hessian c).flip e‖ ≤ (C*d^alpha+A*d)/delta := hh
      _ ≤ (C*d^alpha+A*d^alpha)/delta :=
        div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdPower hA)) hdelta.le
      _ = K*d^alpha := by dsimp only [K]; ring
  have hmix : ∀ w : E, inner ℝ N w=0 →
      ‖(J.hessian x-J.hessian c).flip w‖ ≤ (K*d^alpha)*‖w‖ := by
    intro w hw
    apply hmixD w
    rw [hDcov]
    change ‖fderiv ℝ g c‖*inner ℝ N w=0
    rw [hw,mul_zero]
  have hRhoLip (z : E) (hz : z ∈ U) (w : E) (hw : w ∈ U) :
      |rho z-rho w| ≤ P*‖z-w‖ := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => ((hrho.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)))
      hrhoD hconv hw hz
  have hRhoLipC (z : E) (hz : z ∈ U) : |rho z-rho c| ≤ P*‖z-c‖ :=
    le_on_closure (hRhoLip z hz) (continuousOn_const.sub hrhoC).abs
      (show ContinuousOn (fun w : E => P*‖z-w‖) (closure U) by fun_prop) hcC
  have hdeltaRho : |rho x-rho c| ≤ P*d :=
    le_on_closure hRhoLipC (hrhoC.sub continuousOn_const).abs
      (show ContinuousOn (fun z : E => P*‖z-c‖) (closure U) by fun_prop) hxC
  have hh := actual_closure_full_hessian_from_mixed_two hU hu2 J hrhoC hpos hdet hrho1
    hxC hcC hN hH (show 0 ≤ K*d^alpha by positivity) (hJH x hxC) (hJH c hcC) hmix hdeltaRho
  change ‖J.hessian x-J.hessian c‖ ≤ B*d^alpha
  calc
    _ ≤ 3*(K*d^alpha)+4*(P*d+3*H*(K*d^alpha))*(H+1) := hh
    _ ≤ 3*(K*d^alpha)+4*(P*d^alpha+3*H*(K*d^alpha))*(H+1) := by gcongr
    _ = B*d^alpha := by dsimp only [B]; ring


end PowerConvexity
