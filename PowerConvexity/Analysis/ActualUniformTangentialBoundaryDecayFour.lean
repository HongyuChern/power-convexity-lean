import PowerConvexity.Analysis.ActualUniformTangentialBoundaryExpansionFour
import PowerConvexity.Analysis.ActualUniformRescaledTangentialGradientFour
import PowerConvexity.Analysis.ActualUniformBoundaryDerivativeDecayFour
import PowerConvexity.Analysis.ActualBoundaryFootFour

/-! # Actual tangential derivative decay at the nearest true boundary point

The original-domain affine expansion is combined with the radius-uniform
nonlinear interior estimate on the genuine distance ball. Every constant
precedes the solution, its closure jet, and the defining tangent field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_defining_tangential_uniform_C2_bounds_four
    {U : Set E} {g : E → ℝ} (hg : ContDiff ℝ 3 g) {F : ℝ}
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F)
    {e N : E} (he : ‖e‖=1) (hN : ‖N‖=1) :
    let T := actualDefiningTangentialFieldFour g e N
    ContDiff ℝ 2 T ∧ ∀ x ∈ closure U,
      ‖T x‖ ≤ 2*F ∧ ‖fderiv ℝ T x‖ ≤ 2*F ∧ ‖fderiv ℝ (fderiv ℝ T) x‖ ≤ 2*F := by
  refine ⟨contDiffOn_univ.mp
    (actual_defining_tangential_field_regular_four isOpen_univ hg.contDiffOn e N),?_⟩
  intro x hx
  have h0 := actual_defining_tangential_field_norm_four g e N x
  have h1 := actual_defining_tangential_field_fderiv_bound_four
    ((hg.contDiffAt (x := x)).of_le (by norm_num)) e N
  have h2 := actual_defining_tangential_field_second_fderiv_bound_four (hg.contDiffAt (x := x)) e N
  simp only [he,hN,mul_one] at h0 h1 h2
  exact ⟨h0.trans (mul_le_mul_of_nonneg_left (hg1 x hx) (by norm_num)),
    h1.trans (mul_le_mul_of_nonneg_left (hg2 x hx) (by norm_num)),
    h2.trans (mul_le_mul_of_nonneg_left (hg3 x hx) (by norm_num))⟩

theorem actual_uniform_tangential_nearest_boundary_decay_four
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
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ U, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 → ∀ x ∈ U, infDist x (frontier U) < R →
      let T := actualDefiningTangentialFieldFour g e N
      let c := actualBoundaryFootOnDomainFour U hproper x
      ‖fderiv ℝ (actualClosureTangentialResponseFour J T) x-
        actualClosureTangentialDerivativeFour J T c‖ ≤ C*(infDist x (frontier U))^gamma := by
  obtain ⟨R0,hR0,alpha,ha,ha1,K,hK0,Q,hQ,hexp⟩ :=
    actual_uniform_tangential_boundary_expansion_four hU hconv hK hg hgb hgdef
      hG hH hP hF hg1 hg2 hg3
  obtain ⟨beta,A,hb,hb1,hA,hinterior⟩ := actual_uniform_rescaled_tangential_gradient_four
    hH hD hP hCsrc hG (show 0 ≤ 2*F by positivity)
      (show 0 ≤ 2*F by positivity) (show 0 ≤ 2*F by positivity)
  let gamma := alpha*beta/(1+beta)
  have hgamma : 0 < gamma ∧ gamma < alpha := actual_quotient_interpolation_exponent_positive_four ha hb
  let R := min 1 (R0/2)
  have hR : 0 < R := lt_min zero_lt_one (half_pos hR0)
  let C := 4*(K*5*(5 : ℝ)^alpha)+A
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨R,hR,min_le_left _ _,gamma,hgamma.1,hgamma.2.trans ha1,C,hC,?_⟩
  intro u rho hu hrho J hzero hpos hdet hrhob hJu huH hrhoD hsource e N he hN x hx hxR
  let T := actualDefiningTangentialFieldFour g e N
  let v := actualClosureTangentialResponseFour J T
  let c := actualBoundaryFootOnDomainFour U hproper x
  let d := infDist x (frontier U)
  let r := d/4
  have hd : 0 < d := (actual_boundary_distance_ball_four hU hproper hx).1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hd1 : d ≤ 1 := hxR.le.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := by dsimp only [r]; linarith
  have hfoot := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
  have hc : c ∈ frontier U := hfoot.1
  have hxc : ‖x-c‖=d := by simpa only [dist_eq_norm] using hfoot.2
  have hsmall : (4+1)*r < R0 := by
    have hh : d < R0/2 := hxR.trans_le (min_le_right _ _)
    dsimp only [r]
    linarith
  have hball2 : ball x (2*r) ⊆ U := by
    intro z hz
    apply ball_infDist_compl_subset
    rw [mem_ball,dist_eq_norm,← infDist_frontier_eq_compl_of_mem hU hproper hx]
    have hh : ‖z-x‖ < 2*r := by simpa only [mem_ball,dist_eq_norm] using hz
    dsimp only [r,d] at hh ⊢
    linarith
  have hball : ball x r ⊆ U := (ball_subset_ball (by linarith : r ≤ 2*r)).trans hball2
  obtain ⟨hT,hTb⟩ := actual_defining_tangential_uniform_C2_bounds_four hg hg1 hg2 hg3 he hN
  have hvreg : ContDiffOn ℝ 2 v U :=
    actual_closure_tangential_response_regular_four hU J (hu.of_le (by norm_num)) hT.contDiffOn
  have hrhoLip : ∀ z ∈ U, ∀ w ∈ U, |rho z-rho w| ≤ P*‖z-w‖ := by
    intro z hz w hw
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => ((hrho.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)))
      hrhoD hconv hw hz
  have huD : ∀ z ∈ ball x r, ‖fderiv ℝ u z‖ ≤ G := by
    intro z hz
    rw [← J.derivative_eq (hball hz)]
    exact hJu z (subset_closure (hball hz))
  have hInt := hinterior r hr hr1 x u rho T (hu.mono hball2) (hrho.mono hball2)
    (fun z hz => hdet z (hball2 hz)) (fun z hz => hpos z (hball2 hz))
    (fun z hz => hrhob z (hball2 hz)) (fun z hz => huH z (hball2 hz))
    (fun z hz w hw => hrhoLip z (hball2 hz) w (hball2 hw))
    (fun z hz => hsource z (hball2 hz)) huD hT.contDiffOn
    (fun z hz => (hTb z (subset_closure (hball hz))).1)
    (fun z hz => (hTb z (subset_closure (hball hz))).2.1)
    (fun z hz => (hTb z (subset_closure (hball hz))).2.2)
  have hmod : ∀ z ∈ ball x r, ‖fderiv ℝ v z-fderiv ℝ v x‖ ≤ A*(‖z-x‖/r)^beta := by
    intro z hz
    change ‖fderiv ℝ (actualClosureTangentialResponseFour J T) z-
      fderiv ℝ (actualClosureTangentialResponseFour J T) x‖ ≤ _
    rw [(actual_closure_tangential_response_eventually_eq_four hU J T (hball hz)).fderiv_eq,
      (actual_closure_tangential_response_eventually_eq_four hU J T hx).fderiv_eq]
    exact hInt z hz x (mem_ball_self hr)
  have hv0 : v c=0 := actual_defining_tangential_response_zero_four hU hconv
    (hu.differentiableOn (by norm_num)) J hzero ((hg.contDiffAt (x := c)).of_le (by norm_num))
    (hgb c hc).1 (hgb c hc).2 (hgdef c hc) e N
  have herr := (hexp u rho hu (hrho.of_le (by norm_num)) J hzero hpos hdet
    (fun z hz => (hrhob z hz).1) hJu huH hrhoD e N he hN c hc).2
  have hh := actual_boundary_derivative_decay_four (u := v)
    (L := actualClosureTangentialDerivativeFour J T c) hr hr1
    (by norm_num : (0 : ℝ) ≤ 4) hK0 hA.le ha hb hball
    (by rw [hxc]; dsimp only [r]; linarith : ‖x-c‖ ≤ 4*r) hsmall
    (fun z hz => ((hvreg.contDiffAt (hU.mem_nhds (hball hz))).differentiableAt (by norm_num)))
    (fun z hz hnear => by simpa only [hv0,zero_add] using herr z hz hnear) hmod
  change ‖fderiv ℝ v x-actualClosureTangentialDerivativeFour J T c‖ ≤ C*d^gamma
  have heq : (4*(K*(4+1)*(4+1)^alpha)+A)*r^(alpha*beta/(1+beta))=C*r^gamma := by
    norm_num [C,gamma]
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hr.le (by dsimp only [r]; linarith : r ≤ d) hgamma.1.le) hC)

end PowerConvexity
