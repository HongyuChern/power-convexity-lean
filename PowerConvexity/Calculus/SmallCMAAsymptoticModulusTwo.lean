import PowerConvexity.Calculus.SmallCMAOscillationIterationTwo

/-! # An actual normalized modulus for small-amplitude solutions.
For any requested oscillation factor, a radius and an explicit amplitude
threshold are fixed before the solution. The threshold is quadratic in
that radius, exactly as required by the proved finite iteration.
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

theorem small_CMA_normalized_asymptotic_modulus_two
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ ∀ (w : E → ℝ) (ε : ℝ),
      0 ≤ ε → ε ≤ δ^2/2 →
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
      (∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall 0 1, |w x| ≤ ε) →
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
        dist x y ≤ δ → |w x-w y| ≤ η*ε := by
  obtain ⟨τ,hτ,hτ1,hdecay⟩ := exists_universal_small_CMA_finite_oscillation_decay_two
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one (half_pos hη) hτ1
  let δ : ℝ := (1/4)/(32:ℝ)^N
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδle : δ ≤ 1/4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 32))
  refine ⟨δ,hδ,hδle,?_⟩
  intro w ε hε hsmall hwc hw hpsh hdet habs x hx y _hy hxy
  have hcl : closedBall x (1/4 : ℝ) ⊆ ball (0 : E) 1 := by
    intro z hz
    have hx0 : dist x (0 : E) ≤ 1/2 := hx
    have hzx : dist z x ≤ 1/4 := hz
    have ht := dist_triangle z x (0 : E)
    change dist z (0 : E) < 1
    linarith only [hx0,hzx,ht]
  have hclUnit : closedBall x (1/4 : ℝ) ⊆ closedBall (0 : E) 1 := hcl.trans ball_subset_closedBall
  have hball : ball x (1/4 : ℝ) ⊆ ball (0 : E) 1 := ball_subset_closedBall.trans hcl
  have hstart : compactOsc w (closedBall x (1/4 : ℝ)) ≤ 2*ε := by
    apply compactOsc_le_of_sub_le (isCompact_closedBall _ _)
      ⟨x,mem_closedBall_self (by norm_num)⟩ (hwc.mono hclUnit)
    intro z hz p hp
    have hzv := abs_le.mp (habs z (hclUnit hz))
    have hpv := abs_le.mp (habs p (hclUnit hp))
    linarith only [hzv.2,hpv.1]
  have hthreshold : 2*ε ≤ ((1/4 : ℝ)/(32:ℝ)^N)^2 := by
    change 2*ε ≤ δ^2
    linarith only [hsmall]
  have hdec := hdecay w x (1/4) (2*ε) (by norm_num) (by positivity)
    (hwc.mono hclUnit) (hw.mono hball)
    (fun z hz => hpsh z (hball hz)) (fun z hz => hdet z (hball hz)) hstart N hthreshold
  have hinner : closedBall x δ ⊆ closedBall (0 : E) 1 :=
    (closedBall_subset_closedBall hδle).trans hclUnit
  have hxinner : x ∈ closedBall x δ := mem_closedBall_self hδ.le
  have hyinner : y ∈ closedBall x δ := by simpa only [mem_closedBall,dist_comm] using hxy
  have hdiff := abs_sub_le_compactOsc (isCompact_closedBall x δ) (hwc.mono hinner) hxinner hyinner
  have hlast : τ^N*(2*ε) ≤ η*ε := by
    have hh := mul_le_mul_of_nonneg_right hN.le hε
    nlinarith only [hh]
  exact hdiff.trans (hdec.trans hlast)

end PowerConvexity
