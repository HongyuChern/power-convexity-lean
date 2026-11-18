import PowerConvexity.Analysis.ActualFlatIterationStepFour
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # Constructed boundary-compatible quadratic sequence for one actual PDE
The spatial scale, smallness threshold and Hessian bound precede the input
coefficient and solution. Every polynomial is obtained by the proved PDE step.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_quadratic_sequence_four {lam Lambda alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatIterationInputFour N lam Lambda alpha kappa,
      ∃ S : (n : ℕ) → ActualFlatQuadraticStateFour N D.solution (r^n) ((1/2 : ℝ)^n) M,
        (S 0).polynomial = (fun _ => 0) ∧
        ∀ n : ℕ, ∀ x : E,
          ‖realHessian (S (n+1)).polynomial x-realHessian (S n).polynomial x‖ ≤ (1/2 : ℝ)^n*M := by
  obtain ⟨M,hM,happrox⟩ := actual_flat_elliptic_quadratic_improvement_four
    hlam hLambda (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) halpha
  obtain ⟨Rmax,hRmax,hpow⟩ := actual_positive_power_radius_two halpha
  obtain ⟨r,hr,hr8,hrmax,hstepN⟩ := happrox (1/2) (by norm_num) Rmax hRmax
  have hr1 : r ≤ 1 := by linarith
  have hrpow : r^alpha ≤ (1/2 : ℝ) := hpow r hr.le hrmax
  refine ⟨M,hM,r,hr,hr8,hrpow,?_⟩
  intro N hN
  obtain ⟨delta,hd,hd1,hstep⟩ := hstepN N hN
  let kappa := delta/(1+32*M)
  have hk : 0 < kappa := by dsimp only [kappa]; positivity
  have hsmall : kappa*(1+32*M) ≤ delta := by
    dsimp only [kappa]
    exact (div_mul_cancel₀ _ (by positivity : (1+32*M) ≠ 0)).le
  have hk1 : kappa ≤ 1 := by
    have hh : kappa ≤ kappa*(1+32*M) := by nlinarith [mul_nonneg hk.le hM.le]
    exact hh.trans (hsmall.trans hd1)
  refine ⟨kappa,hk,hk1,?_⟩
  intro D
  let P := fun n : ℕ => ActualFlatQuadraticStateFour N D.solution (r^n) ((1/2 : ℝ)^n) M
  have hHzero (x : E) : realHessian (fun _ : E => (0 : ℝ)) x = 0 := by
    unfold realHessian
    simp
  have hTzero (x : E) :
      (realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x).trace=0 := by
    have he : realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x=0 := by
      ext i j
      unfold realBlockHessian
      rw [hHzero]
      rfl
    rw [he,Matrix.trace_zero]
  let S0 : P 0 := {
    polynomial := fun _ => 0
    quadratic := (quadraticSubmodule E).zero_mem
    zero := fun _ _ => rfl
    trace := hTzero
    hessian := by
      rw [hHzero]
      have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖=0 := norm_zero
      rw [hz]
      norm_num
    error := by intro x hx; simpa using D.solution_bound x (by simpa using hx)
  }
  have hnext (n : ℕ) (S : P n) : ∃ T : P (n+1),
      ∀ x : E, ‖realHessian T.polynomial x-realHessian S.polynomial x‖ ≤ (1/2 : ℝ)^n*M := by
    have hRn := pow_pos hr n
    have hbn : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
    have hR1 : r^n ≤ 1 := pow_le_one₀ hr.le hr1
    have hb1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hRa : (r^n)^alpha ≤ (1/2 : ℝ)^n :=
      actual_geometric_rpow_half_bound_two hr.le halpha.le hrpow n (pow_nonneg hr.le n) le_rfl
    have hh := actual_flat_quadratic_iteration_step_four halpha hk.le hRn hR1 hbn hb1 hM hRa
      hsmall hd1 D hstep S
    have he : (1/2 : ℝ)^n/2=(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
    rw [← (pow_succ r n),he] at hh
    exact hh
  let next (n : ℕ) (S : P n) : P (n+1) := Classical.choose (hnext n S)
  let S : (n : ℕ) → P n := fun n => Nat.rec (motive := P) S0 (fun n S => next n S) n
  refine ⟨S,rfl,?_⟩
  intro n x
  change ‖realHessian (next n (S n)).polynomial x-realHessian (S n).polynomial x‖ ≤ _
  exact Classical.choose_spec (hnext n (S n)) x

end PowerConvexity
