import PowerConvexity.Analysis.ActualUniformTangentialBoundaryDecayFour
import PowerConvexity.Analysis.ActualUniformDefiningNormalFour

/-! # Actual common mixed-Hessian decay at the nearest true boundary point

The actual defining field equals |Dg| times a unit tangent vector at the
boundary point. Its correction terms use only the genuine C2 bound and the
fixed defining function. Thus the mixed Hessian modulus is a conclusion.
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

theorem actual_covector_kernel_bound_of_unit_four
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ e : E, ‖e‖=1 → D e=0 → ‖H.flip e‖ ≤ C) :
    ∀ w : E, D w=0 → ‖H.flip w‖ ≤ C*‖w‖ := by
  intro w hw
  by_cases hw0 : w=0
  · simp only [hw0,map_zero,norm_zero,mul_zero,le_refl]
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let e : E := ‖w‖⁻¹ • w
  have he : ‖e‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwn),inv_mul_cancel₀ hwn.ne']
  have hDe : D e=0 := by simp only [e,map_smul,hw,smul_zero]
  have hwe : w=‖w‖ • e := by
    simp only [e,smul_smul,mul_inv_cancel₀ hwn.ne',one_smul]
  calc
    ‖H.flip w‖ = ‖w‖*‖H.flip e‖ := by
      conv_lhs => rw [hwe]
      rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hwn]
    _ ≤ ‖w‖*C := mul_le_mul_of_nonneg_left (hunit e he hDe) hwn.le
    _ = _ := mul_comm _ _

theorem actual_uniform_mixed_nearest_boundary_decay_four
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
      ∀ J : ClosureC2Jet u U,
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
      let c := actualBoundaryFootOnDomainFour U hproper x
      ∀ w : E, fderiv ℝ g c w=0 →
        ‖(realHessian u x-J.hessian c).flip w‖ ≤ C*(infDist x (frontier U))^gamma*‖w‖ := by
  obtain ⟨R,hR,hR1,gamma,hgamma,hgamma1,C,hC,hdecay⟩ :=
    actual_uniform_tangential_nearest_boundary_decay_four hU hconv hK hproper hg hgb hgdef
      hG hH hP hF hD hCsrc hg1 hg2 hg3
  obtain ⟨delta,hdelta,hmargin⟩ := actual_uniform_defining_normal_margin_four hK
    (hg.of_le (by norm_num)) (fun c hc => (hgb c hc).2)
  let A := 2*H*(2*F)+G*(2*F)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let K := (C+A)/delta
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨R,hR,hR1,gamma,hgamma,hgamma1,K,hK0,?_⟩
  intro u rho hu hrho J hzero hpos hdet hrhob hJu hJH hrhoD hsource x hx hxR
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
  have hresp := hdecay u rho hu hrho J hzero hpos hdet hrhob hJu huH hrhoD hsource e N he hN x hx hxR
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
