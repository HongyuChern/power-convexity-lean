import PowerConvexity.Analysis.ActualHarmonicHessianL2Two
import PowerConvexity.Calculus.HarmonicCubicTaylorFour
import PowerConvexity.Analysis.ActualHarmonicHalfBallQuadraticTwo

/-! # Actual harmonic L2 data have a uniform cubic Taylor remainder

The polynomial and the cubic constant are chosen uniformly from the original
weak harmonic function, without a qualitative choice of modulus radius.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_weak_harmonic_L2_cubic_taylor_two :
    ∃ M > 0, ∃ L > 0, ∀ u : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 u →
      ContinuousOn u (ball (0 : F) 1) →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ r : ℝ, 0 < r → r ≤ (1/16 : ℝ) →
          ∀ x ∈ closedBall (0 : F) r, |u x-q x| ≤ L*r^3 := by
  obtain ⟨C,hC,hMoser⟩ := actual_continuous_weak_unitBall_L2_bound_two
    (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1))
  obtain ⟨M0,hM0,L0,hL0,hApprox⟩ := classical_harmonic_unitBall_universal_cubic_taylor_four
  let B := C+1
  have hB : 0 < B := by dsimp only [B]; linarith
  refine ⟨16*B*M0,by positivity,64*B*L0,by positivity,?_⟩
  intro u hu hc uw hnorm
  have hharm := actual_identity_weak_continuous_is_classical_two isOpen_ball hu hc
  let G : F → ℝ := fun x => B⁻¹*u ((1/4 : ℝ) • x)
  have hmaps (x : F) (hx : x ∈ closedBall (0 : F) 1) :
      (1/4 : ℝ) • x ∈ ball (0 : F) (1/2 : ℝ) := by
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
    linarith
  have hGc : ContinuousOn G (closedBall (0 : F) 1) := by
    apply continuousOn_const.mul
    exact hc.comp (by fun_prop : ContinuousOn (fun x : F => (1/4 : ℝ) • x) (closedBall 0 1))
      (fun x hx => ball_subset_ball (by norm_num) (hmaps x hx))
  have hGh : InnerProductSpace.HarmonicOnNhd G (ball (0 : F) 1) := by
    have hd := classical_harmonic_dilate_to_unitBall_four (by norm_num : (0:ℝ)<1/4)
      (hharm.mono (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1)))
    have he : G = B⁻¹ • (fun x : F => u ((1/4 : ℝ) • x)) := rfl
    rw [he]
    exact hd.const_smul
  have hGb (x : F) (hx : x ∈ closedBall (0 : F) 1) : |G x| ≤ 1 := by
    have hm := hMoser u hu (hc.mono (ball_subset_ball (by norm_num))) uw _ (hmaps x hx)
    have hb : |u ((1/4 : ℝ) • x)| ≤ B :=
      hm.trans ((mul_le_mul_of_nonneg_left hnorm hC).trans (by dsimp only [B]; linarith))
    change |B⁻¹*u ((1/4 : ℝ) • x)| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hB)]
    calc
      B⁻¹*|u ((1/4 : ℝ) • x)| ≤ B⁻¹*B := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
  obtain ⟨hq,ht,hH,herror⟩ := hApprox G hGc hGh hGb
  let q : F → ℝ := fun x => B*secondTaylorPolynomialZero G ((4 : ℝ) • x)
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  have hG0 := (hGh 0 (mem_ball_self (by norm_num))).1
  have heH (x : F) : realHessian q x = (16*B) • realHessian G 0 := by
    change realHessian (fun y => B*secondTaylorPolynomialZero G ((4 : ℝ) • y)) x = _
    rw [CHS.Calculus.realHessian_const_mul,actual_realHessian_comp_scalar_four 4 hqC.contDiffAt,
      secondTaylorPolynomialZero_hessian hG0]
    norm_num [smul_smul,mul_comm]
  refine ⟨q,IsQuadraticPolynomial_const_mul (IsQuadraticPolynomial_comp_scalar hq 4) B,?_,?_,?_⟩
  · intro x
    have hh := actual_classical_harmonic_trace_zero_two hGh (mem_ball_self (by norm_num))
    change realBlockTraceFormFour (realHessian q x) = 0
    rw [heH,map_smul]
    change (16*B)*(realBlockHessian realDirections imagDirections G 0).trace = 0
    rw [hh,mul_zero]
  · intro x
    rw [heH,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 16*B)]
    exact mul_le_mul_of_nonneg_left hH (by positivity)
  · intro r hr hr16 x hx
    have hxrho : (4 : ℝ) • x ∈ closedBall (0 : F) (4*r) := by
      have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith
    have he := mul_le_mul_of_nonneg_left
      (herror (4*r) (by positivity) (by linarith) _ hxrho) hB.le
    have hpoint : u x-q x = B*(G ((4 : ℝ) • x)-secondTaylorPolynomialZero G ((4 : ℝ) • x)) := by
      simp only [q,G,smul_smul,show (1/4 : ℝ)*4=1 by norm_num,one_smul]
      field_simp
      <;> ring
    rw [hpoint,abs_mul,abs_of_pos hB]
    calc
      B*|G ((4 : ℝ) • x)-secondTaylorPolynomialZero G ((4 : ℝ) • x)|
          ≤ B*(L0*(4*r)^3) := he
      _ = (64*B*L0)*r^3 := by ring


theorem actual_harmonic_halfBall_L2_cubic_taylor_two :
    ∃ M > 0, ∃ L > 0, ∀ v : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v →
      ContinuousOn v (ball (0 : F) (1/2 : ℝ)) →
      ∀ vw : MemW1pWitness 2 v (ball (0 : F) (1/2 : ℝ)), ‖vw.memLp.toLp v‖ ≤ 2 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ r : ℝ, 0 < r → r ≤ (1/32 : ℝ) →
          ∀ x ∈ closedBall (0 : F) r, |v x-q x| ≤ L*r^3 := by
  obtain ⟨M,hM,L,hL,ha⟩ := actual_weak_harmonic_L2_cubic_taylor_two
  refine ⟨32*M,by positivity,64*L,by positivity,?_⟩
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
  · intro r hr hr32 x hx
    have hxr : (2 : ℝ) • x ∈ closedBall (0 : F) (2*r) := by
      have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
      norm_num
      linarith
    have hh := mul_le_mul_of_nonneg_left
      (herror (2*r) (by positivity) (by linarith) _ hxr) (by norm_num : (0 : ℝ) ≤ 8)
    have he : v x-q x = 8*(W ((2 : ℝ) • x)-q0 ((2 : ℝ) • x)) := by
      simp only [q,W,vr,rescaleToUnitBall,zero_add,smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul]
      ring
    rw [he,abs_mul]
    norm_num
    nlinarith only [hh]

end PowerConvexity
