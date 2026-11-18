import PowerConvexity.Analysis.ActualHarmonicHessianL2Two
import PowerConvexity.Calculus.HarmonicQuadraticPrescribedRadiusFour

/-! # Uniform actual harmonic quadratic approximation from unit L2 data.
The radius and Hessian constant are selected before the weak harmonic
function. The approximating polynomial is its actual rescaled second
Taylor polynomial, and its actual block trace is zero everywhere.
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

theorem actual_weak_harmonic_L2_quadratic_below_radius_two :
    ∃ M > 0, ∀ eta > 0, ∀ R > 0, ∃ r > 0, r ≤ (1/16 : ℝ) ∧ r ≤ R ∧
      ∀ u : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 u →
      ContinuousOn u (ball (0 : F) 1) →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ closedBall (0 : F) r, |u x-q x| ≤ eta*r^2 := by
  obtain ⟨C,hC,hMoser⟩ := actual_continuous_weak_unitBall_L2_bound_two
    (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1))
  obtain ⟨M0,hM0,hApprox⟩ := classical_harmonic_unitBall_quadratic_below_radius_four
  let B := C+1
  have hB : 0 < B := by dsimp only [B]; linarith
  refine ⟨16*B*M0,by positivity,?_⟩
  intro eta heta R hR
  obtain ⟨rho,hrho,hrhoq,hrhoR,ha⟩ := hApprox (eta/(16*B)) (by positivity) (4*R) (by positivity)
  refine ⟨rho/4,by positivity,by linarith,by linarith,?_⟩
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
  obtain ⟨hq,ht,hH,herror⟩ := ha G hGc hGh hGb
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
  · intro x hx
    have hxrho : (4 : ℝ) • x ∈ closedBall (0 : F) rho := by
      have hn : ‖x‖ ≤ rho/4 := by simpa only [mem_closedBall,dist_zero_right] using hx
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith
    have he := mul_le_mul_of_nonneg_left (herror _ hxrho) hB.le
    have hpoint : u x-q x = B*(G ((4 : ℝ) • x)-secondTaylorPolynomialZero G ((4 : ℝ) • x)) := by
      simp only [q,G,smul_smul,show (1/4 : ℝ)*4=1 by norm_num,one_smul]
      field_simp
      <;> ring
    rw [hpoint,abs_mul,abs_of_pos hB]
    calc
      B*|G ((4 : ℝ) • x)-secondTaylorPolynomialZero G ((4 : ℝ) • x)|
          ≤ B*((eta/(16*B))*rho^2) := he
      _ = eta*(rho/4)^2 := by field_simp <;> ring

end PowerConvexity
