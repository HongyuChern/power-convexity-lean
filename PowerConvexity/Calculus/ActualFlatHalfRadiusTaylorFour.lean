import PowerConvexity.Calculus.ActualFlatBoundaryTaylorFour
import PowerConvexity.Calculus.HarmonicQuadraticHalfBallFour

/-! # Boundary-compatible Taylor approximation at the actual compactness radius -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_harmonic_flat_half_boundary_quadratic_below_radius_four :
    ∃ M > 0, ∀ eta > 0, ∀ Rmax > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r ≤ Rmax ∧
      ∀ N : E, ‖N‖=1 → ∀ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) →
      InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) →
      (∀ x ∈ closedBall (0 : E) (1/2), inner ℝ N x=0 → g x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |g x-q x| ≤ eta*r^2 := by
  obtain ⟨M,hM,happrox⟩ := actual_harmonic_flat_boundary_quadratic_below_radius_four
  refine ⟨4*M,mul_pos (by norm_num) hM,?_⟩
  intro eta heta Rmax hRmax
  obtain ⟨rho,hrho,hrhoq,hrhomax,ha⟩ := happrox (eta/4) (by positivity) (2*Rmax) (by positivity)
  refine ⟨rho/2,half_pos hrho,by linarith,by linarith,?_⟩
  intro N hN g hgC hgH hg0 hgb
  let G : E → ℝ := fun x => g ((1/2 : ℝ) • x)
  have hmapC : MapsTo (fun x : E => (1/2 : ℝ) • x)
      (actualFlatClosedUpperBallFour N 1) (actualFlatClosedUpperBallFour N (1/2)) := by
    intro x hx
    constructor
    · have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith
    · change 0 ≤ inner ℝ N ((1/2 : ℝ) • x)
      rw [inner_smul_right]
      exact mul_nonneg (by norm_num) hx.2
  have hmapU : MapsTo (fun x : E => (1/2 : ℝ) • x)
      (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N (1/2)) := by
    intro x hx
    constructor
    · have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx.1
      simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith
    · change 0 < inner ℝ N ((1/2 : ℝ) • x)
      rw [inner_smul_right]
      exact mul_pos (by norm_num) hx.2
  have hGC : ContinuousOn G (actualFlatClosedUpperBallFour N 1) :=
    hgC.comp (by fun_prop : ContinuousOn (fun x : E => (1/2 : ℝ) • x) _) hmapC
  have hGH : InnerProductSpace.HarmonicOnNhd G (actualFlatUpperBallFour N 1) := by
    have hh := classical_harmonic_affine_scalar_pullback_two
      (actualFlatUpperBallFour_isOpen N (1/2)) hgH (0 : E) (1/2)
    intro x hx
    simpa only [zero_add] using hh x (by simpa only [mem_preimage,zero_add] using hmapU hx)
  have hG0 (x : E) (hx : x ∈ closedBall (0 : E) 1) (hn : inner ℝ N x=0) : G x=0 := by
    have hm := hmapC (show x ∈ actualFlatClosedUpperBallFour N 1 from ⟨hx,hn.ge⟩)
    apply hg0 _ hm.1
    simp only [inner_smul_right,hn,mul_zero]
  obtain ⟨p,hp,hp0,hpt,hpH,hpa⟩ := ha N hN G hGC hGH hG0 (fun x hx => hgb _ (hmapC hx))
  let q : E → ℝ := fun x => p ((2 : ℝ) • x)
  have hpC := IsQuadraticPolynomial_contDiff hp 2
  have hH (x : E) : realHessian q x = (4 : ℝ) • realHessian p ((2 : ℝ) • x) := by
    simpa only [q,show (2 : ℝ)^2=4 by norm_num] using
      actual_realHessian_comp_scalar_four 2 hpC.contDiffAt (x := x)
  refine ⟨q,IsQuadraticPolynomial_comp_scalar hp 2,?_,?_,?_,?_⟩
  · intro x hx
    apply hp0
    simp only [inner_smul_right,hx,mul_zero]
  · intro x
    change realBlockTraceFormFour (realHessian q x)=0
    rw [hH,map_smul]
    change (4 : ℝ)*(realBlockHessian realDirections imagDirections p ((2 : ℝ) • x)).trace=0
    rw [hpt,mul_zero]
  · intro x
    rw [hH,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<4)]
    exact mul_le_mul_of_nonneg_left (hpH _) (by norm_num)
  · intro x hx
    have hx2 : (2 : ℝ) • x ∈ actualFlatClosedUpperBallFour N rho := by
      constructor
      · have hn : ‖x‖ ≤ rho/2 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
        simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ)<2)]
        linarith
      · change 0 ≤ inner ℝ N ((2 : ℝ) • x)
        rw [inner_smul_right]
        exact mul_nonneg (by norm_num) hx.2
    have hh := hpa _ hx2
    simp only [G,smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul] at hh
    exact hh.trans_eq (by ring)

end PowerConvexity
