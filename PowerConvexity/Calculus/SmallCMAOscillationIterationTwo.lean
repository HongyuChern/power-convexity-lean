import PowerConvexity.Calculus.SmallCMACompactOscillationTwo

/-! # Finite actual oscillation iteration with checked thresholds.
The terminal-radius smallness condition is sufficient for every
intermediate invocation; arbitrary infinite iteration is not asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem exists_universal_small_CMA_finite_oscillation_decay_two :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∀ (w : E → ℝ) (c : E) (r ε : ℝ),
      0 < r → 0 ≤ ε → ContinuousOn w (closedBall c r) → ContDiffOn ℝ 2 w (ball c r) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).det = 1) →
      compactOsc w (closedBall c r) ≤ ε →
      ∀ N : ℕ, ε ≤ (r/(32:ℝ)^N)^2 →
      compactOsc w (closedBall c (r/(32:ℝ)^N)) ≤ τ^N*ε := by
  obtain ⟨τ,hτ,hτ1,hstep⟩ := exists_universal_small_CMA_compact_oscillation_contraction_two
  refine ⟨τ,hτ,hτ1,?_⟩
  intro w c r ε hr hε hwc hw hpsh hdet hstart N
  induction N with
  | zero =>
    intro _hsmall
    simpa only [pow_zero,div_one,one_mul] using hstart
  | succ N ih =>
    intro hsmall
    let ρ : ℝ := r/(32:ℝ)^N
    have hρ : 0 < ρ := by dsimp only [ρ]; positivity
    have hρr : ρ ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 32))
    have hrad : r/(32:ℝ)^(N+1) = ρ/32 := by
      dsimp only [ρ]
      rw [pow_succ,div_mul_eq_div_div]
    have hprev : ε ≤ ρ^2 := by
      rw [hrad] at hsmall
      have hle : ρ/32 ≤ ρ := by linarith only [hρ]
      exact hsmall.trans ((sq_le_sq₀ (by positivity : 0 ≤ ρ/32) hρ.le).mpr hle)
    have hdec : compactOsc w (closedBall c ρ) ≤ τ^N*ε := ih hprev
    have hpow : τ^N*ε ≤ ε := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hε
    have hthreshold : compactOsc w (closedBall c ρ) ≤ ρ^2 := hdec.trans (hpow.trans hprev)
    have hball : ball c ρ ⊆ ball c r := ball_subset_ball hρr
    have hclosed : closedBall c ρ ⊆ closedBall c r := closedBall_subset_closedBall hρr
    have hh := hstep w c ρ hρ (hwc.mono hclosed) (hw.mono hball)
      (fun x hx => hpsh x (hball hx)) (fun x hx => hdet x (hball hx)) hthreshold
    rw [hrad]
    calc
      compactOsc w (closedBall c (ρ/32)) ≤ τ*compactOsc w (closedBall c ρ) := hh
      _ ≤ τ*(τ^N*ε) := mul_le_mul_of_nonneg_left hdec hτ.le
      _ = τ^(N+1)*ε := by rw [pow_succ]; ring

end PowerConvexity
