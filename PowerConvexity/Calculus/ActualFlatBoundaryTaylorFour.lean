import PowerConvexity.Calculus.ActualHarmonicFlatReflectionFour
import PowerConvexity.Calculus.HarmonicQuadraticPrescribedRadiusFour
import CHS.Calculus.HessianLocality

/-! # Actual boundary-compatible harmonic quadratic approximation
The quadratic is the actual Taylor polynomial of the proved odd extension.
It vanishes on the whole normal hyperplane and is harmonic. The radius and
Hessian bound are selected before the normal and the harmonic function.
-/
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

theorem actual_secondTaylor_flat_zero_of_odd_four {N : E} (hN : ‖N‖=1)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g 0)
    (hodd : (fun x => g (actualFlatReflectionFour N x)) =ᶠ[𝓝 (0 : E)] (fun x => -g x)) :
    ∀ v : E, inner ℝ N v=0 → secondTaylorPolynomialZero g v=0 := by
  let R := actualFlatReflectionFour N
  have hzero : g 0=0 := by
    have hh := hodd.self_of_nhds
    simp only [map_zero] at hh
    linarith
  have hreg : ContDiffAt ℝ 2 g (R 0) := by simpa only [map_zero] using hg
  have hDc : fderiv ℝ (fun x => g (R x)) 0 = (fderiv ℝ g 0).comp R.toContinuousLinearEquiv.toContinuousLinearMap := by
    have hh := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp 0
      R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    simpa only [map_zero,Function.comp_def,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hh.fderiv
  have hD (v : E) : fderiv ℝ g 0 (R v) = -fderiv ℝ g 0 v := by
    have he := hodd.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fun x => g (R x)) 0 = fderiv ℝ (fun x => -g x) 0 at he
    rw [hDc,fderiv_fun_neg] at he
    simpa only [ContinuousLinearMap.comp_apply,_root_.neg_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      congrArg (fun L : E →L[ℝ] ℝ => L v) he
  have hH (v : E) : realHessian g 0 (R v) (R v) = -realHessian g 0 v v := by
    calc
      realHessian g 0 (R v) (R v) = realHessian (fun x => g (R x)) 0 v v := by
        simpa only [map_zero] using (realHessian_comp_linearIsometry R hreg v v).symm
      _ = realHessian (fun x => -g x) 0 v v :=
        congrArg (fun H : E →L[ℝ] E →L[ℝ] ℝ => H v v) (realHessian_eq_of_eventuallyEq hodd)
      _ = -realHessian g 0 v v := by simp only [realHessian_neg,_root_.neg_apply]
  intro v hv
  have hRv : R v=v := actualFlatReflectionFour_fixed hN hv
  have hd := hD v
  have hh := hH v
  rw [hRv] at hd hh
  have hd0 : fderiv ℝ g 0 v=0 := by linarith
  have hh0 : realHessian g 0 v v=0 := by linarith
  simp only [secondTaylorPolynomialZero,hzero,hd0,_root_.smul_apply,smul_eq_mul,hh0,mul_zero,add_zero]

theorem actual_harmonic_flat_boundary_quadratic_below_radius_four :
    ∃ M > 0, ∀ eta > 0, ∀ Rmax > 0, ∃ r > 0, r ≤ (1/4 : ℝ) ∧ r ≤ Rmax ∧
      ∀ N : E, ‖N‖=1 → ∀ u : E → ℝ,
      ContinuousOn u (actualFlatClosedUpperBallFour N 1) →
      InnerProductSpace.HarmonicOnNhd u (actualFlatUpperBallFour N 1) →
      (∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |u x-q x| ≤ eta*r^2 := by
  obtain ⟨M,hM,happ⟩ := classical_harmonic_unitBall_quadratic_below_radius_four
  refine ⟨M,hM,?_⟩
  intro eta heta Rmax hRmax
  obtain ⟨r,hr,hrq,hrmax,ha⟩ := happ eta heta Rmax hRmax
  refine ⟨r,hr,hrq,hrmax,?_⟩
  intro N hN u huC huH hu0 hub
  let v := actualFlatOddExtensionFour N u
  obtain ⟨hvC,hvH,hvreg⟩ := actual_zero_flat_harmonic_odd_reflection_four hN huC huH hu0
  have hvb (x : E) (hx : x ∈ closedBall (0 : E) 1) : |v x| ≤ 1 := by
    by_cases hn : 0 ≤ inner ℝ N x
    · rw [show v x=u x from actualFlatOddExtensionFour_upper N u hn]
      exact hub x ⟨hx,hn⟩
    · change |if 0 ≤ inner ℝ N x then u x else -u (actualFlatReflectionFour N x)| ≤ 1
      rw [if_neg hn,abs_neg]
      apply hub
      refine ⟨?_,?_⟩
      · simpa only [mem_closedBall,dist_zero_right,(actualFlatReflectionFour N).norm_map] using hx
      · change 0 ≤ inner ℝ N (actualFlatReflectionFour N x)
        rw [actualFlatReflectionFour_normal hN]
        exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hn))
  obtain ⟨hqp,hqt,hqH,hqe⟩ := ha v hvC hvH hvb
  have hv2 : ContDiffAt ℝ 2 v 0 := (hvH 0 (mem_ball_self (by norm_num))).1
  have ho : (fun x => v (actualFlatReflectionFour N x)) =ᶠ[𝓝 (0 : E)] (fun x => -v x) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ)<1))] with x hx
    exact actualFlatOddExtensionFour_odd hN u hu0 (ball_subset_closedBall hx)
  refine ⟨secondTaylorPolynomialZero v,hqp,actual_secondTaylor_flat_zero_of_odd_four hN hv2 ho,hqt,?_,?_⟩
  · intro x
    rw [secondTaylorPolynomialZero_hessian hv2]
    exact hqH
  · intro x hx
    have hxe := hqe x hx.1
    have hx1 : x ∈ closedBall (0 : E) 1 := closedBall_subset_closedBall (hrq.trans (by norm_num)) hx.1
    rw [show v x=u x from actualFlatOddExtensionFour_upper N u hx.2] at hxe
    exact hxe

end PowerConvexity
