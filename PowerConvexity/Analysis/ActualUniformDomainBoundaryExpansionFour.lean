import PowerConvexity.Analysis.ActualCommonDomainGraphPhysicalInputFour
import PowerConvexity.Analysis.ActualUniformFixedNormalPhysicalChartsFour
import PowerConvexity.Analysis.ActualContinuousDomainAffinePullbackFour
import PowerConvexity.Analysis.ActualPhysicalBoundaryQuadraticBoundsFour
import PowerConvexity.Analysis.ActualPhysicalInverseGraphSideFour

/-! # Actual uniform original-domain boundary expansions for continuous Holder loads

The original domain, defining function and common elliptic/Holder bounds
determine one radius and all polynomial bounds before the actual equation
and actual solution. The physical equation, true zero trace, fixed inward
normal and original frozen contraction are all constructed and identified.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_continuous_domain_boundary_expansion_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ c ∈ frontier U, f c=0) (hDf : ∀ c ∈ frontier U, fderiv ℝ f c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ f z < 0)
    {lam Lambda alpha Ka Kf B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ R > 0, ∃ M ≥ 0, ∃ T ≥ 0, ∃ G₀ ≥ 0,
      ∀ D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf,
      (∀ x ∈ frontier U, D.solution x=0) →
      (∀ x ∈ closure U, |D.solution x| ≤ B) →
      (∀ x ∈ closure U, |D.source x| ≤ F) →
      ∃ J : ActualContinuousDomainBoundaryExpansionFour D R M T,
        ∀ c ∈ frontier U, ‖fderiv ℝ (J.polynomial c) c‖ ≤ G₀ := by
  classical
  let N : E := EuclideanSpace.single 0 1
  have hN : ‖N‖=1 := by simp only [N,EuclideanSpace.norm_single,norm_one]
  obtain ⟨r,hr,hr1,K,hKpos,hcharts⟩ := actual_uniform_fixed_normal_physical_boundary_charts_four
    hU hK hf hf0 hDf hdef hN hlam hLambda
  let Bmap := Real.sqrt Lambda
  let I := (Real.sqrt lam)⁻¹
  have hBmap : 0 < Bmap := Real.sqrt_pos.mpr hLambda
  have hI : 0 < I := inv_pos.mpr (Real.sqrt_pos.mpr hlam)
  let ell := lam/(max 1 Bmap)^2
  let cap := Lambda*(max 1 I)^2
  let Ka' := I^2*Ka*(r*Bmap)^alpha
  let Kf' := r^2*Kf*(r*Bmap)^alpha
  let L := 1+(1 : ℝ)
  let A₀ := 1+Ka'*L^alpha
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hKa' : 0 ≤ Ka' := by dsimp [Ka']; positivity
  have hKf' : 0 ≤ Kf' := by dsimp [Kf']; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hL : 0 < L := by norm_num [L]
  obtain ⟨R0,hR0,hR01,M0,hM0,G0,hG0,H0,hH0,hpolynomial⟩ :=
    actual_common_graph_original_prescribed_holder_expansion_four
      (show 0 < ell/L^2 by positivity) (show 0 < cap*L^2 by positivity) halpha halpha1
      (show 0 ≤ 2*L*A₀*(2*K)+L^2*(Ka'*L^alpha) by positivity)
      (show 0 ≤ 16*((Ka'*L^alpha)*K+A₀*(2*K)) by positivity)
      (show 0 ≤ Kf'*L^alpha by positivity) (show 0 ≤ 16*A₀*K by positivity)
      hB (show 0 ≤ r^2*F by positivity) hN hKpos.le
  let Q := I/r
  have hQ : 0 < Q := div_pos hI hr
  let R := R0/(2*Q)
  have hR : 0 < R := div_pos hR0 (by positivity)
  refine ⟨R,hR,M0*Q^2*Q^alpha,by positivity,H0*Q^2,by positivity,G0*Q,by positivity,?_⟩
  intro D hzero hbound hsource
  have haC := actual_holder_matrix_entries_continuous_four halpha D.holder
  have haPositive := actual_positive_elliptic_coefficient_on_closure_four hU D.coeff haC D.positive
  have haBounds := actual_elliptic_bounds_on_closure_four hU D.coeff haC
  have hpoint : ∀ c ∈ frontier U, ∃ P : E → ℝ,
      IsQuadraticPolynomial P ∧ ‖realHessian P 0‖ ≤ H0*Q^2 ∧
      (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian P c i j) = -D.source c ∧
      (∀ x ∈ U, ‖x-c‖ < R → |D.solution x-P x| ≤ (M0*Q^2*Q^alpha)*‖x-c‖^2*‖x-c‖^alpha) ∧
      ‖fderiv ℝ P c‖ ≤ G0*Q := by
    intro c hc
    have hcC := frontier_subset_closure hc
    have hlo : ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (D.coeff.a c) v) := by
      intro v
      exact (mul_le_mul_of_nonneg_right D.lower (sq_nonneg _)).trans (haBounds c hcC v).1
    have hhi : ∀ v : E, inner ℝ v (matMulE (D.coeff.a c) v) ≤ Lambda*‖v‖^2 := by
      intro v
      exact ((haBounds c hcC v).2).trans (mul_le_mul_of_nonneg_right D.upper (sq_nonneg _))
    obtain ⟨G,hfreeze,hGB,hGI,rho,hrho0,hD0,hinv,hreg,hLip,hThird,hmap,hFlatZero⟩ :=
      hcharts c hc (D.coeff.a c) (haPositive c hcC) hlo hhi
    let Phi : E → E := fun z => c+G (r • z)
    let V : Set E := Phi ⁻¹' U
    have hPhiC : Continuous Phi := by fun_prop
    have hV : IsOpen V := hU.preimage hPhiC
    have hPhi : MapsTo Phi V U := fun _ hz => hz
    have hPhiClosure := hPhi.closure hPhiC
    let D' := D.affinePullback hU c G hr halpha.le hKa hKf hBmap.le hI.le hGB hGI
    have hfrozen : D'.coeff.a 0=1 := by
      change actualLinearCongruenceMatrixTwo G (D.coeff.a (c+G (r • (0 : E))))=1
      simpa only [smul_zero,map_zero,add_zero] using hfreeze
    have hzero' : ∀ z ∈ frontier V, D'.solution z=0 :=
      D.affinePullback_zero hU c G hr halpha.le hKa hKf hBmap.le hI.le hGB hGI hzero
    have hbound' : ∀ z ∈ closure V, |D'.solution z| ≤ B :=
      fun z hz => hbound _ (hPhiClosure hz)
    have hreg1 (z : E) (hz : z ∈ closedBall (0 : E) 1) :
        ContDiffAt ℝ 3 rho z ∧ ‖fderiv ℝ rho z‖ ≤ 1 ∧ ‖realHessian rho z‖ ≤ K :=
      hreg z (closedBall_subset_closedBall (by norm_num) hz)
    let Dp := actualCommonDomainGraphPhysicalInputFour hV hell halpha halpha1.le hKa' hKf'
      (by norm_num : (0 : ℝ) ≤ 1) hKpos.le hKpos.le hKpos.le D' hN
      (fun z hz => (hreg z hz).1) hrho0 hD0 hfrozen hinv hmap
      (fun z hz => (hreg1 z hz).2.1) (fun z hz => (hreg1 z hz).2.2)
      (fun z hz w hw => (hLip z (closedBall_subset_closedBall (by norm_num) hz)
        w (closedBall_subset_closedBall (by norm_num) hw)).1)
      (fun z hz w hw => (hLip z (closedBall_subset_closedBall (by norm_num) hz)
        w (closedBall_subset_closedBall (by norm_num) hw)).2)
      hzero' hbound'
    have hDpSource : Dp.source 0=r^2*D.source c := by
      change r^2*D.source (c+G (r • actualGraphShearFour N rho 0))=r^2*D.source c
      simp only [actualGraphShearFour,hrho0,zero_smul,add_zero,smul_zero,map_zero]
    have hf0 : |Dp.source 0| ≤ r^2*F := by
      rw [hDpSource,abs_mul,abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left (hsource c hcC) (sq_nonneg r)
    obtain ⟨p,hp,hpG,hpH,hpTrace,hpError⟩ := hpolynomial rho
      (fun z hz => (hreg1 z hz).1) hrho0 hD0 (fun z hz => (hreg1 z hz).2.2)
      hThird hinv Dp hf0 D'.solution rfl D'.coeff.a hfrozen rfl
    let P := actualPhysicalQuadraticTwo G (G.symm c) r p
    have hPquad := actual_physical_quadratic_isQuadratic_two G (G.symm c) r hp
    have hPbounds := actual_physical_boundary_quadratic_bounds_four G c hr hI.le hG0 hH0 hGI hp hpG hpH
    have hPfreeze : (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian P c i j) = -D.source c := by
      have htrace : (realBlockHessian realDirections imagDirections p 0).trace = -(r^2*D.source c) := by
        simpa only [hDpSource] using hpTrace 0
      simpa only [G.apply_symm_apply] using
        actual_physical_quadratic_frozen_equation_two G (G.symm c) hr hfreeze hp htrace
    refine ⟨P,hPquad,hPbounds.2 0,hPfreeze,?_,hPbounds.1⟩
    intro x hx hxR
    let z : E := r⁻¹ • G.symm (x-c)
    have hzQ : ‖z‖ ≤ Q*‖x-c‖ := actual_affine_inverse_coordinate_norm_four G c x hr hGI
    have hzR : ‖z‖ < R0 := by
      have hh : Q*‖x-c‖ < Q*R := mul_lt_mul_of_pos_left hxR hQ
      have he : Q*R=R0/2 := by dsimp [R]; field_simp
      exact (hzQ.trans_lt (hh.trans_eq he)).trans (by linarith)
    have hz1 : ‖z‖ ≤ 1 := hzR.le.trans hR01
    have hside := actual_original_domain_inverse_graph_side_four G hr hN hrho0
      (fun w hw => (hreg1 w hw).1.differentiableAt (by norm_num))
      (fun w hw => (hreg1 w hw).2.1) hinv hmap hx hz1
    have he := hpError z (mem_closedBall.mpr (by simpa only [dist_zero_right] using hzR.le)) hside.le
    have hrecover : Phi z=x := by
      dsimp only [Phi,z]
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,G.apply_symm_apply]
      abel
    have hPvalue : P x=p z := by
      dsimp only [P,actualPhysicalQuadraticTwo,z]
      rw [map_sub]
    have hDvalue : D'.solution z=D.solution x := by
      change D.solution (Phi z)=D.solution x
      rw [hrecover]
    rw [hDvalue,← hPvalue] at he
    have hsq : ‖z‖^2 ≤ Q^2*‖x-c‖^2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hzQ 2).trans_eq (mul_pow _ _ _)
    have hpow : ‖z‖^alpha ≤ Q^alpha*‖x-c‖^alpha :=
      (Real.rpow_le_rpow (norm_nonneg _) hzQ halpha.le).trans_eq (Real.mul_rpow hQ.le (norm_nonneg _))
    exact he.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hsq hM0) hpow
      (Real.rpow_nonneg (norm_nonneg _) alpha) (by positivity)).trans_eq (by ring))
  let P : E → E → ℝ := fun c => if hc : c ∈ frontier U then Classical.choose (hpoint c hc) else fun _ => 0
  have hP (c : E) (hc : c ∈ frontier U) := Classical.choose_spec (hpoint c hc)
  have hPeq (c : E) (hc : c ∈ frontier U) : P c=Classical.choose (hpoint c hc) := dif_pos hc
  refine ⟨{
    polynomial := P
    quadratic := fun c hc => by rw [hPeq c hc]; exact (hP c hc).1
    hessian_bound := fun c hc => by rw [hPeq c hc]; exact (hP c hc).2.1
    frozen := fun c hc => by rw [hPeq c hc]; exact (hP c hc).2.2.1
    remainder := fun c hc => by rw [hPeq c hc]; exact (hP c hc).2.2.2.1
  },?_⟩
  intro c hc
  change ‖fderiv ℝ (P c) c‖ ≤ G0*Q
  rw [hPeq c hc]
  exact (hP c hc).2.2.2.2

end PowerConvexity
