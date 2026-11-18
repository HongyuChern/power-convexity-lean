import PowerConvexity.Analysis.ActualWeakL2ScalingTwo
import PowerConvexity.Analysis.ActualScalarWeakLinearOperationsTwo
import PowerConvexity.Analysis.ActualHarmonicQuadraticL2Two

/-! # Actual harmonic quadratic approximation on the replacement half ball.
The normalization uses the exact four-dimensional L2 scaling and the same
weak harmonic function. The radius is uniform before the function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_homogeneous_weak_smul_two {U : Set F} (hU : IsOpen U)
    {A : EllipticCoeff (2+2) U} {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution A u) (c : ℝ) :
    IsHomogeneousWeakSolution A (fun x => c*u x) := by
  apply (actual_scalar_weak_zero_iff_homogeneous_two A _).mp
  have hh := actual_scalar_weak_smul_two hU
    ((actual_scalar_weak_zero_iff_homogeneous_two A u).mpr hu) c
  simpa only [mul_zero] using hh

theorem actual_harmonic_halfBall_L2_quadratic_approximation_two :
    ∃ M > 0, ∀ eta > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧
      ∀ v : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v →
      ContinuousOn v (ball (0 : F) (1/2 : ℝ)) →
      ∀ vw : MemW1pWitness 2 v (ball (0 : F) (1/2 : ℝ)), ‖vw.memLp.toLp v‖ ≤ 2 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ closedBall (0 : F) r, |v x-q x| ≤ eta*r^2 := by
  obtain ⟨M,hM,happ⟩ := actual_weak_harmonic_L2_quadratic_approximation_two
  refine ⟨32*M,by positivity,?_⟩
  intro eta heta
  obtain ⟨rho,hrho,hrhob,ha⟩ := happ (eta/32) (by positivity)
  refine ⟨rho/2,by positivity,by linarith,?_⟩
  intro v hv hc vw hn
  let vr : F → ℝ := rescaleToUnitBall (x₀ := (0 : F)) (R := (1/2 : ℝ)) v
  let rwit := vw.rescaleToUnitBall (by norm_num : (0 : ℝ) < 1/2)
  have hrw : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 vr := by
    exact rescaleToUnitBall_isHomogeneousWeakSolution (by norm_num : (0 : ℝ)<1/2)
      (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 hv
  have hrn : ‖rwit.memLp.toLp vr‖ ≤ 8 := by
    have hh := actual_scalar_L2_rescale_squared_two (by norm_num : (0 : ℝ)<1/2)
      vw.memLp rwit.memLp
    change ‖rwit.memLp.toLp vr‖^2 = ((1/2 : ℝ)^4)⁻¹*‖vw.memLp.toLp v‖^2 at hh
    rw [show ((1/2 : ℝ)^4)⁻¹=16 by norm_num] at hh
    nlinarith [norm_nonneg (vw.memLp.toLp v),norm_nonneg (rwit.memLp.toLp vr)]
  let W : F → ℝ := fun x => (1/8 : ℝ)*vr x
  let ww := rwit.smul (1/8 : ℝ)
  have hWw : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 W :=
    actual_homogeneous_weak_smul_two isOpen_ball hrw (1/8 : ℝ)
  let hrmem : MemLp vr 2 (volume.restrict (ball (0 : F) 1)) := rwit.memLp
  have hWn : ‖ww.memLp.toLp W‖ ≤ 1 := by
    change ‖(hrmem.const_smul (1/8 : ℝ)).toLp ((1/8 : ℝ) • vr)‖ ≤ 1
    rw [MemLp.toLp_const_smul (1/8 : ℝ) hrmem,norm_smul,Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ)<1/8)]
    nlinarith only [hrn]
  have hWc : ContinuousOn W (ball (0 : F) 1) := by
    apply continuousOn_const.mul
    apply hc.comp (by fun_prop : ContinuousOn (fun x : F => (0 : F)+(1/2 : ℝ) • x) (ball 0 1))
    intro x hx
    have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    simp only [mem_ball,zero_add,dist_zero_right,norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  obtain ⟨q0,hq0,ht0,hH0,herror⟩ := ha W hWw hWc ww hWn
  let q : F → ℝ := fun x => 8*q0 ((2 : ℝ) • x)
  have hqc := IsQuadraticPolynomial_contDiff hq0 2
  have hH (x : F) : realHessian q x = (32 : ℝ) • realHessian q0 ((2 : ℝ) • x) := by
    change realHessian (fun y => 8*q0 ((2 : ℝ) • y)) x = _
    rw [CHS.Calculus.realHessian_const_mul,actual_realHessian_comp_scalar_four 2 hqc.contDiffAt]
    norm_num [smul_smul]
  refine ⟨q,IsQuadraticPolynomial_const_mul (IsQuadraticPolynomial_comp_scalar hq0 2) 8,?_,?_,?_⟩
  · intro x
    change realBlockTraceFormFour (realHessian q x) = 0
    rw [hH,map_smul]
    change (32 : ℝ)*(realBlockHessian realDirections imagDirections q0 ((2 : ℝ) • x)).trace = 0
    rw [ht0,mul_zero]
  · intro x
    rw [hH,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<32)]
    exact mul_le_mul_of_nonneg_left (hH0 _) (by norm_num : (0 : ℝ) ≤ 32)
  · intro x hx
    have hxr : (2 : ℝ) • x ∈ closedBall (0 : F) rho := by
      have hn : ‖x‖ ≤ rho/2 := by simpa only [mem_closedBall,dist_zero_right] using hx
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
      norm_num
      linarith
    have hh := mul_le_mul_of_nonneg_left (herror _ hxr) (by norm_num : (0 : ℝ) ≤ 8)
    have he : v x-q x = 8*(W ((2 : ℝ) • x)-q0 ((2 : ℝ) • x)) := by
      simp only [q,W,vr,rescaleToUnitBall,zero_add,smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul]
      ring
    rw [he,abs_mul]
    norm_num
    nlinarith only [hh]

end PowerConvexity
