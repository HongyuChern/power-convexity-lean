import PowerConvexity.Analysis.ActualFlatDriftIterationStepFour
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # An actual boundary quadratic sequence for the full drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_quadratic_sequence_four {lam Lambda alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∃ K > 0, ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa, D.source 0=0 →
      ∃ S : (n : ℕ) → ActualFlatDriftQuadraticStateFour N D.solution (D.drift 0) (D.source 0)
          (r^n) ((1/2 : ℝ)^n) M K,
        (S 0).polynomial = (fun _ => 0) ∧
        ∀ n : ℕ,
          ‖fderiv ℝ (S (n+1)).polynomial 0-fderiv ℝ (S n).polynomial 0‖ ≤ (1/2 : ℝ)^n*r^n*K ∧
          ∀ x : E, ‖realHessian (S (n+1)).polynomial x-realHessian (S n).polynomial x‖ ≤ (1/2 : ℝ)^n*M := by
  obtain ⟨M0,hM0,happrox⟩ := actual_flat_drift_frozen_quadratic_improvement_four hlam hLambda
  obtain ⟨Rmax,hRmax,hpow⟩ := actual_positive_power_radius_two halpha
  obtain ⟨r,hr,hr8,hrmax,K,hK,hstepN⟩ := happrox (1/2) (by norm_num) Rmax hRmax
  let M := M0+1/2
  have hM : 0 < M := by dsimp only [M]; linarith
  have hr1 : r ≤ 1 := hr8.trans (by norm_num)
  have hrpow : r^alpha ≤ (1/2 : ℝ) := hpow r hr.le hrmax
  refine ⟨M,hM,r,hr,hr8,hrpow,K,hK,?_⟩
  intro N hN
  obtain ⟨delta,hd,hd1,hstep⟩ := hstepN N hN
  let kappa := delta/(1+34*M+2*K)
  have hk : 0 < kappa := by dsimp only [kappa]; positivity
  have hsmall : kappa*(1+34*M+2*K) ≤ delta := by
    dsimp only [kappa]
    exact (div_mul_cancel₀ _ (by positivity : (1+34*M+2*K) ≠ 0)).le
  have hk1 : kappa ≤ 1 := by
    have hh : kappa ≤ kappa*(1+34*M+2*K) :=
      by nlinarith [mul_nonneg hk.le hM.le,mul_nonneg hk.le hK.le]
    exact hh.trans (hsmall.trans hd1)
  refine ⟨kappa,hk,hk1,?_⟩
  intro D hf0
  let P := fun n : ℕ => ActualFlatDriftQuadraticStateFour N D.solution (D.drift 0) (D.source 0)
    (r^n) ((1/2 : ℝ)^n) M K
  have hDz : fderiv ℝ (fun _ : E => (0 : ℝ)) 0=0 := by simp
  have hHz (x : E) : realHessian (fun _ : E => (0 : ℝ)) x=0 := by
    unfold realHessian
    simp
  have hTz (x : E) : (realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x).trace=0 := by
    have he : realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x=0 := by
      ext i j
      unfold realBlockHessian
      rw [hHz]
      rfl
    rw [he,Matrix.trace_zero]
  let S0 : P 0 := {
    polynomial := fun _ => 0
    quadratic := (quadraticSubmodule E).zero_mem
    zero := fun _ _ => rfl
    frozen := by simp only [hTz,hDz,hf0,_root_.zero_apply,add_zero,neg_zero]
    gradient := by rw [hDz]; simp
    hessian := by
      rw [hHz]
      have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖=0 := norm_zero
      rw [hz]
      norm_num
    error := by intro x hx; simpa using D.solution_bound x (by simpa using hx)
  }
  have hnext (n : ℕ) (S : P n) : ∃ T : P (n+1),
      ‖fderiv ℝ T.polynomial 0-fderiv ℝ S.polynomial 0‖ ≤ (1/2 : ℝ)^n*r^n*K ∧
      ∀ x : E, ‖realHessian T.polynomial x-realHessian S.polynomial x‖ ≤ (1/2 : ℝ)^n*M := by
    have hRn := pow_pos hr n
    have han : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
    have hR1 : r^n ≤ 1 := pow_le_one₀ hr.le hr1
    have hRa : (r^n)^alpha ≤ (1/2 : ℝ)^n :=
      actual_geometric_rpow_half_bound_two hr.le halpha.le hrpow n (pow_nonneg hr.le n) le_rfl
    have hh := actual_flat_drift_quadratic_iteration_step_four hN halpha halpha1 hk.le
      hRn hR1 han hM hK hRa hsmall D hstep S
    have he : (1/2 : ℝ)^n/2=(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
    rw [← (pow_succ r n),he] at hh
    exact hh
  let next (n : ℕ) (S : P n) : P (n+1) := Classical.choose (hnext n S)
  let S : (n : ℕ) → P n := fun n => Nat.rec (motive := P) S0 (fun n S => next n S) n
  refine ⟨S,rfl,?_⟩
  intro n
  exact Classical.choose_spec (hnext n (S n))

end PowerConvexity
