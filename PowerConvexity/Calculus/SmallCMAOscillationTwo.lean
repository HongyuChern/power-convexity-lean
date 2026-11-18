import PowerConvexity.Calculus.SmallValueOffCenterDecayTwo
import PowerConvexity.Analysis.CMADeviationLevelToPointTwo

/-! # One actual flat oscillation improvement on the fixed inner ball.
The same determinant-one solution supplies the contacts, level sets,
identity-Laplacian supersolution and pointwise deficit. All constants
are fixed before the function and its small oscillation amplitude.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem exists_universal_small_CMA_oscillation_improvement_two :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ x ∈ closedBall 0 1, 0 ≤ w x ∧ w x ≤ ε) →
      (∀ x ∈ closedBall (0 : E) (1/32 : ℝ), κ*ε ≤ w x) ∨
      (∀ x ∈ closedBall (0 : E) (1/32 : ℝ), w x ≤ (1-κ)*ε) := by
  classical
  obtain ⟨M,θ,hM,hθ,hθ1,hdecay⟩ := exists_universal_off_center_superlevel_decay_two
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1/2) hθ1
  have hMp : 0 < M := by linarith only [hM]
  have hMk : 0 < M^k := pow_pos hMp _
  let K : ℝ := weakHarnackMeanConstant (2+2) (by norm_num) 1
  let V : ℝ := volume.real (closedBall (0 : E) (1/8 : ℝ))
  have hK : 0 < K := weakHarnackMeanConstant_pos (by norm_num) 1
  have hV : 0 < V := by
    dsimp only [V]
    rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume]
    exact ENNReal.toReal_pos
      (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1/8)).ne'
      measure_ball_lt_top.ne
  let κ : ℝ := min (1/2) (min (1/(6144*M^k)) (V/(4*K)))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκhalf : κ ≤ 1/2 := min_le_left _ _
  have hκseed : κ ≤ 1/(6144*M^k) := (min_le_right _ _).trans (min_le_left _ _)
  have hκmean : κ ≤ V/(4*K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ,hκ,by linarith only [hκhalf],?_⟩
  intro w hwc hw hpsh hdet ε hε hε1 hbound
  by_cases hall : ∀ x ∈ closedBall (0 : E) (1/32 : ℝ), κ*ε ≤ w x
  · exact Or.inl hall
  push_neg at hall
  obtain ⟨z,hz,hzsmall⟩ := hall
  right
  let a : ℝ := ε/(6*M^k)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hscale : M^k*a = ε/6 := by dsimp only [a]; field_simp <;> ring
  have hseedbound : κ*ε ≤ a/1024 := by
    calc
      κ*ε ≤ (1/(6144*M^k))*ε := mul_le_mul_of_nonneg_right hκseed hε.le
      _ = a/1024 := by dsimp only [a]; field_simp; ring
  have hsmall : w z ≤ a/1024 := hzsmall.le.trans hseedbound
  have hthreshold : M^k*a ≤ 1 := by rw [hscale]; linarith only [hε1]
  have hlevels := hdecay w hwc hw hdet (fun x hx => (hbound x hx).1)
    a ha z hz hsmall k hthreshold
  have hlevelidentity : 3*(M^k*a) = ε/2 := by rw [hscale]; ring
  rw [hlevelidentity] at hlevels
  have hlevel : volume.real {x | x ∈ closedBall (0 : E) (1/8 : ℝ) ∧ ε/2 < w x} ≤
      volume.real (closedBall (0 : E) (1/8 : ℝ))/2 := by
    apply hlevels.trans
    have hh := mul_le_mul_of_nonneg_right hk.le hV.le
    dsimp only [V] at hh
    linarith only [hh]
  have hwball : ContDiffOn ℝ 2 w (ball (0 : E) 1) := hw.mono ball_subset_interior_closedBall
  have hpshball : ∀ x ∈ ball (0 : E) 1,
      (1+complexHessian realDirections imagDirections w x).PosSemidef :=
    fun x hx => hpsh x (ball_subset_interior_closedBall hx)
  have hdetball : ∀ x ∈ ball (0 : E) 1,
      (1+complexHessian realDirections imagDirections w x).det = 1 :=
    fun x hx => hdet x (ball_subset_interior_closedBall hx)
  intro y hy
  have hyinner : y ∈ ball (0 : E) (1/8 : ℝ) := (closedBall_subset_ball (by norm_num)) hy
  have hdef := actual_shifted_CMA_half_level_forces_deficit_two hwball hpshball hdetball hε.le
    (fun x hx => (hbound x (ball_subset_closedBall hx)).2) hlevel hyinner
  have hκprod : K*κ ≤ V/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*K)).mp hκmean
    nlinarith only [hh]
  have hmul := mul_le_mul_of_nonneg_right hκprod hε.le
  have hdrop : K*(κ*ε) ≤ K*(ε-w y) := by
    change (ε/4)*V ≤ K*(ε-w y) at hdef
    nlinarith only [hdef,hmul]
  have hh := le_of_mul_le_mul_left hdrop hK
  linarith only [hh]

end PowerConvexity
