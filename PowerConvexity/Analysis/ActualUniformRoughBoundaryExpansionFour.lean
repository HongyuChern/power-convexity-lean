import PowerConvexity.Analysis.ActualUniformRoughGraphQuotientFour
import PowerConvexity.Analysis.ActualUniformFixedNormalPhysicalChartsFour
import PowerConvexity.Analysis.ActualUniformInverseGraphLinearRemainderFour
import PowerConvexity.Analysis.ActualPhysicalInverseGraphSideFour

/-! # A genuine common first-order boundary expansion for rough coefficients

The fixed true defining function supplies common physical charts by applying
the geometric construction to the identity matrix. The actual coefficient
is transported afterwards; no boundary continuity modulus is required for
it. Radius, exponent, remainder and slope bound precede the equation and all
boundary points.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_rough_domain_boundary_expansion_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hg0 : ∀ c ∈ frontier U, g c=0) (hDg : ∀ c ∈ frontier U, fderiv ℝ g c≠0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {lam Lambda F M : ℝ} (hlam : 0 < lam) (hLambda : lam ≤ Lambda)
    (hF : 0 ≤ F) (hM : 0 ≤ M) :
    ∃ R > 0, ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0, ∃ Q ≥ 0,
      ∀ D : ActualRoughDomainDirichletDataFour U lam Lambda F M,
      ∀ c ∈ frontier U, ∃ L : E →L[ℝ] ℝ, ‖L‖ ≤ Q ∧
        ∀ x ∈ U, ‖x-c‖ < R →
          |D.solution x-L (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha := by
  let N : E := EuclideanSpace.single 0 1
  have hN : ‖N‖=1 := by simp only [N,EuclideanSpace.norm_single,norm_one]
  obtain ⟨r,hr,hr1,H,hH,hcharts⟩ := actual_uniform_fixed_normal_physical_boundary_charts_four
    hU hK hg hg0 hDg hdef hN (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r0,hr0,_,alpha,ha,ha1,C0,hC0,hquot⟩ :=
    actual_uniform_rough_domain_graph_quotient_four hlam hLambda
      (by norm_num : (0 : ℝ) ≤ 1) hH.le hF hM
  obtain ⟨R0,hR0,hR01,K,hK0,hrem⟩ := actual_uniform_inverse_graph_linear_remainder_four
    hr0 hC0.le hC0.le hH.le ha.le ha1.le
  let Q := 1/r
  have hQ : 0 < Q := one_div_pos.mpr hr
  let R := R0/(2*Q)
  have hR : 0 < R := div_pos hR0 (by positivity)
  refine ⟨R,hR,alpha,ha,ha1,K*Q*Q^alpha,by positivity,C0*Q,by positivity,?_⟩
  intro D c hc
  have hidentity (v : E) : matMulE (1 : Mat) v=v := by
    ext i
    simp only [matMulE_apply,Matrix.one_mulVec]
  have henergy (v : E) : inner ℝ v (matMulE (1 : Mat) v)=1*‖v‖^2 := by
    rw [hidentity,real_inner_self_eq_norm_sq,one_mul]
  obtain ⟨G,_,hGB,hGI,rho,hrho0,hD0,hinv,hreg,_,_,hmap,_⟩ :=
    hcharts c hc 1 Matrix.PosDef.one (fun v => (henergy v).ge) (fun v => (henergy v).le)
  simp only [Real.sqrt_one,inv_one] at hGB hGI
  let Phi : E → E := fun z => c+G (r • z)
  let V := Phi ⁻¹' U
  have hPhiC : Continuous Phi := by fun_prop
  have hV : IsOpen V := hU.preimage hPhiC
  let D0 := D.affinePullback hU c G hr hGB hGI
  let D' : ActualRoughDomainDirichletDataFour V lam Lambda F M :=
    D0.enlarge (by simp) (by simp)
      (by
        have hh : r^2 ≤ 1 := by nlinarith
        exact (mul_le_mul_of_nonneg_right hh hF).trans_eq (one_mul _)) le_rfl
  have hreg1 (z : E) (hz : z ∈ closedBall (0 : E) 1) :
      ContDiffAt ℝ 3 rho z ∧ ‖fderiv ℝ rho z‖ ≤ 1 ∧ ‖realHessian rho z‖ ≤ H :=
    hreg z (closedBall_subset_closedBall (by norm_num) hz)
  obtain ⟨q,hq,herr⟩ := hquot N hN V hV D' rho (fun z hz => (hreg z hz).1) hinv hmap
    (fun z hz => (hreg1 z (ball_subset_closedBall hz.1)).2.1)
    (fun z hz => (hreg1 z (ball_subset_closedBall hz.1)).2.2)
  have he := hrem N hN rho D'.solution q hq
    (fun z hz => (hreg1 z hz).1.of_le (by norm_num))
    (fun z hz => (hreg1 z hz).2.2) hrho0 hD0 hinv herr
  let L : E →L[ℝ] ℝ := (q • innerSL ℝ N).comp (r⁻¹ • G.symm.toContinuousLinearMap)
  have hL : ‖L‖ ≤ C0*Q := by
    have hqN : ‖q • innerSL ℝ N‖ ≤ C0 := by
      rw [norm_smul,Real.norm_eq_abs,innerSL_apply_norm,hN,mul_one]
      exact hq
    have hInv : ‖r⁻¹ • G.symm.toContinuousLinearMap‖ ≤ Q := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (mul_le_mul_of_nonneg_left hGI (inv_pos.mpr hr).le).trans_eq (by simp [Q,one_div])
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hqN hInv (norm_nonneg _) hC0.le)
  refine ⟨L,hL,?_⟩
  intro x hx hxR
  let z : E := r⁻¹ • G.symm (x-c)
  have hzQ : ‖z‖ ≤ Q*‖x-c‖ := actual_affine_inverse_coordinate_norm_four G c x hr hGI
  have hzR : ‖z‖ < R0 := by
    have hh : Q*‖x-c‖ < Q*R := mul_lt_mul_of_pos_left hxR hQ
    have heq : Q*R=R0/2 := by dsimp [R]; field_simp
    exact (hzQ.trans_lt (hh.trans_eq heq)).trans (by linarith)
  have hz1 : ‖z‖ ≤ 1 := hzR.le.trans hR01
  have hside := actual_original_domain_inverse_graph_side_four G hr hN hrho0
    (fun w hw => (hreg1 w hw).1.differentiableAt (by norm_num))
    (fun w hw => (hreg1 w hw).2.1) hinv hmap hx hz1
  have herror := he z (mem_closedBall.mpr (by simpa only [dist_zero_right] using hzR.le)) hside.le
  have hrecover : Phi z=x := by
    dsimp only [Phi,z]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,G.apply_symm_apply]
    abel
  have hDvalue : D'.solution z=D.solution x := by
    change D.solution (Phi z)=D.solution x
    rw [hrecover]
  have hLvalue : L (x-c)=q*inner ℝ N z := by
    simp only [L,z,ContinuousLinearMap.comp_apply,_root_.smul_apply,innerSL_apply_apply,smul_eq_mul,ContinuousLinearEquiv.coe_coe]
  rw [hDvalue,← hLvalue] at herror
  have hpow : ‖z‖^alpha ≤ Q^alpha*‖x-c‖^alpha :=
    (Real.rpow_le_rpow (norm_nonneg _) hzQ ha.le).trans_eq (Real.mul_rpow hQ.le (norm_nonneg _))
  exact herror.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hzQ hK0) hpow
    (Real.rpow_nonneg (norm_nonneg _) alpha) (by positivity)).trans_eq (by ring))

end PowerConvexity
