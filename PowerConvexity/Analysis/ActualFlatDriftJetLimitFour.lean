import PowerConvexity.Analysis.ActualFlatDriftQuadraticSequenceFour
import PowerConvexity.Analysis.ActualFlatQuadraticLimitFour

/-! # Actual limiting jets preserve the full frozen drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quadratic_limit_frozen_drift_four
    {Q : ℕ → E → ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ} {l : E →L[ℝ] ℝ}
    (hQ : ∀ n, IsQuadraticPolynomial (Q n))
    (hH : Tendsto (fun n => realHessian (Q n) 0) atTop (𝓝 H))
    (hl : Tendsto (fun n => fderiv ℝ (Q n) 0) atTop (𝓝 l))
    (b0 : E) (f0 c : ℝ)
    (ht : ∀ n, (realBlockHessian realDirections imagDirections (Q n) 0).trace+
      fderiv ℝ (Q n) 0 b0 = -f0) :
    (realBlockHessian realDirections imagDirections (actualQuadraticJetFunctionTwo c l H) 0).trace+
      fderiv ℝ (actualQuadraticJetFunctionTwo c l H) 0 b0 = -f0 := by
  let e : (Fin 2 ⊕ Fin 2) → E := Sum.elim realDirections imagDirections
  have hc : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => ∑ i, B (e i) (e i)) := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_eval_const (e i)).comp (continuous_eval_const (e i))
  have hlim := ((hc.tendsto H).comp hH).add (((continuous_eval_const b0).tendsto l).comp hl)
  change Tendsto (fun n => (realBlockHessian realDirections imagDirections (Q n) 0).trace+
    fderiv ℝ (Q n) 0 b0) atTop (𝓝 ((∑ i, H (e i) (e i))+l b0)) at hlim
  have hconst : Tendsto (fun n => (realBlockHessian realDirections imagDirections (Q n) 0).trace+
      fderiv ℝ (Q n) 0 b0) atTop (𝓝 (-f0)) := by
    simpa only [ht] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => -f0) atTop (𝓝 (-f0)))
  have he := tendsto_nhds_unique hlim hconst
  obtain ⟨_,_,hD,hess⟩ := actual_quadratic_jet_reconstruction_two c l H
    (actual_realHessian_limit_symmetry_two hQ hH)
  rw [hD]
  change (∑ i, realHessian (actualQuadraticJetFunctionTwo c l H) 0 (e i) (e i))+l b0 = -f0
  simpa only [hess 0] using he

theorem actual_flat_drift_sequence_fullJet_increments_four
    {N b0 : E} {u : E → ℝ} {f0 r M K : ℝ} (hr : 0 < r) (hM : 0 < M) (hK : 0 < K)
    (S : (n : ℕ) → ActualFlatDriftQuadraticStateFour N u b0 f0 (r^n) ((1/2 : ℝ)^n) M K)
    (hi : ∀ n, ‖fderiv ℝ (S (n+1)).polynomial 0-fderiv ℝ (S n).polynomial 0‖ ≤ (1/2 : ℝ)^n*r^n*K ∧
      ∀ x : E, ‖realHessian (S (n+1)).polynomial x-realHessian (S n).polynomial x‖ ≤ (1/2 : ℝ)^n*M) :
    ∀ n, ActualScalarQuadraticIncrementTwo (M+K) r n (S n).polynomial (S (n+1)).polynomial := by
  intro n
  refine ⟨?_,?_,?_⟩
  · rw [(S (n+1)).zero 0 (by simp),(S n).zero 0 (by simp),sub_self,abs_zero]
    positivity
  · exact (hi n).1.trans (mul_le_mul_of_nonneg_left (by linarith : K ≤ M+K) (by positivity))
  · intro x
    exact ((hi n).2 x).trans (mul_le_mul_of_nonneg_left (by linarith : M ≤ M+K) (by positivity))

end PowerConvexity
