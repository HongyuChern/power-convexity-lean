import PowerConvexity.Analysis.ActualWeakDriftOscillationFour
import PowerConvexity.Analysis.ActualVanishingHolderCompactnessFour

/-! # An actual weak compactness theorem allowing nonzero column divergence -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_weak_drift_uniform_subsequence_four
    (A : ℕ → NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {L M : ℝ}
    (hL : ∀ n, (A n).1.Λ ≤ L) (hM : 0 ≤ M)
    (k : ℕ → ℝ) (hk : ∀ n, 0 < k n) (hk1 : ∀ n, k n ≤ 1)
    (hkt : Tendsto k atTop (𝓝 0))
    (hA : ∀ n i j, ContDiffOn ℝ 1 (fun y => (A n).1.a y i j) (ball (0 : E) 1))
    (hAC : ∀ n i j, ContinuousOn (fun y => (A n).1.a y i j) (closedBall (0 : E) 1))
    (b : ℕ → E → E) (hb : ∀ n, ContinuousOn (b n) (closedBall (0 : E) 1))
    (hdiv : ∀ n x, x ∈ ball (0 : E) 1 → actualCoefficientColumnDivergenceFour (A n).1.a x=b n x)
    (htrace : ∀ n x, x ∈ ball (0 : E) 1 → 1 ≤ ((A n).1.a x).trace)
    (hsmall : ∀ n x, x ∈ ball (0 : E) 1 → ‖b n x‖ ≤ 1/2)
    (f u : ℕ → E → ℝ) (hf : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : E) 1)))
    (hu : ∀ n, ActualScalarWeakEquationTwo (A n).1 (f n) (u n))
    (huC : ∀ n, ContinuousOn (u n) (ball (0 : E) (1/2 : ℝ)))
    (hub : ∀ n, ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |u n x| ≤ M)
    (hfb : ∀ n, ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f n x| ≤ k n) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (closedBall (0 : E) (1/4 : ℝ)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (closedBall (0 : E) (1/4 : ℝ)) ∧
      ∀ x ∈ closedBall (0 : E) (1/4 : ℝ), |g x| ≤ M := by
  let K : Set E := closedBall (0 : E) (1/4 : ℝ)
  have hK : K ⊆ ball (0 : E) (1/2 : ℝ) := closedBall_subset_ball (by norm_num)
  have hval (n : ℕ) : ∀ x ∈ K, |u n x| ≤ M := by
    have hh := actual_continuous_abs_bound_of_ae_four isOpen_ball
      (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)) (huC n) continuousOn_const (hub n)
    exact fun x hx => hh x (hK hx)
  have hC0 : 0 ≤ CHolderMoser (2+2) :=
    (C_harnack_nonneg (by norm_num : 2 < ((2+2 : ℕ) : ℝ))).trans C_harnack_le_C_holder_Moser
  have hL0 : 0 ≤ L := (A 0).1.Λ_nonneg.trans (hL 0)
  have hCb (n : ℕ) : actualUniformMoserBoundFour L (M+k n) ≤ actualUniformMoserBoundFour L (M+1) := by
    dsimp only [actualUniformMoserBoundFour]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl M) (hk1 n)) (by positivity)
  have hosc (n : ℕ) := actual_weak_drift_source_oscillation_four (A n) (hL n) hM (hk n)
    (hA n) (hAC n) (hb n) (hdiv n) (htrace n) (hsmall n) (hf n) (hu n) (huC n) (hub n) (hfb n)
  apply actual_compact_uniform_subsequence_of_vanishing_holder_error_four
    (isCompact_closedBall (0 : E) (1/4 : ℝ)) u (fun n => (huC n).mono hK)
    (Real.exp_pos _ : 0 < actualUniformMoserExponentFour L) hval (fun n => 2*k n)
    (by simpa only [mul_zero] using hkt.const_mul 2)
  intro n x hx y hy
  exact (hosc n x (hK hx) y (hK hy)).trans (add_le_add (le_refl (2*k n))
    (mul_le_mul_of_nonneg_right (hCb n) (Real.rpow_nonneg (norm_nonneg _) _)))

end PowerConvexity
