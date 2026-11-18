import PowerConvexity.Calculus.TracePowerUniformSecondJet
import PowerConvexity.Calculus.TracePowerEigenvalueLimit
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Actual uniform trace-root second derivatives and limit interchange

The IFT eigenvalue derivative is independently proved in the inherited
source. The new quantitative estimate proves uniform convergence to it;
pointwise identification is not used as a substitute for uniformity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators ContDiff Topology
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tracePowerRoot_second_eq_mixedJet {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j : ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (n : ℕ)
    (hreal : ∀ y ∈ U, (K y^(n+2)).trace.im = 0) (a b c d : E) :
    dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x =
      traceRootMixedJet k (matrixDZ a b K x) (matrixDZ c d K x)
        (matrixDZ c d (matrixDZ a b K) x) n := by
  have he := paper_B4_1_tracePowerRoot hU hK hx (n+1)
    (by simpa [add_assoc] using hreal)
    (by rw [hdiag]; exact real_diagonal_trace_power_pos k i hi h0 (n+1+1)) a b c d
  rw [he, hdiag, real_diagonal_trace_power, Complex.ofReal_re]
  simp only [traceRootMixedJet, trace_diagonal_power_mul, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel, add_assoc]
  norm_num
  ring

theorem tracePowerRoot_second_uniform_error_actual [CompleteSpace E]
    {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j : ℂ)))
    (h0 : ∀ j, 0 ≤ k j) {q δ M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) (hki : δ ≤ k i)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hr : ∀ j, j ≠ i → k j/k i ≤ q)
    (htrace : ∀ n : ℕ, ∀ y ∈ U, (K y^(n+2)).trace.im = 0)
    (hspec : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0)
    (a b c d : E)
    (hX : ∀ l m, ‖matrixDZ a b K x l m‖ ≤ M1)
    (hY : ∀ l m, ‖matrixDZ c d K x l m‖ ≤ M1)
    (hZ : ∀ j, ‖matrixDZ c d (matrixDZ a b K) x j j‖ ≤ M2) (n : ℕ) :
    ‖dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x -
      dz c d (dz a b (fun y => (largestRealEigenvalue (K y) : ℂ))) x‖ ≤
      traceRootSecondErrorConstant (Fintype.card ι) q δ M1 M2*((n : ℝ)+1)*q^n := by
  have hi : 0 < k i := hδ.trans_le hki
  have hgap : ∀ j, j ≠ i → k j < k i := fun j hj =>
    (div_lt_one hi).mp ((hr j hj).trans_lt hq1)
  have hp := paper_B3_2_tracePowerRoot_second_limit hU hK hx k i hdiag hi h0 hgap htrace a b c d
  have ha := paper_B3_3_tracePowerRoot_second_limit_actual_largest
    hU hK hx k i hdiag hi h0 hgap htrace hspec a b c d
  have hid : traceRootMixedJetLimit k i (matrixDZ a b K x) (matrixDZ c d K x)
      (matrixDZ c d (matrixDZ a b K) x) =
      dz c d (dz a b (fun y => (largestRealEigenvalue (K y) : ℂ))) x :=
    tendsto_nhds_unique hp ha
  rw [tracePowerRoot_second_eq_mixedJet hU hK hx k i hdiag hi h0 n (htrace n) a b c d, ← hid]
  exact traceRootMixedJet_uniform_error_le k i h0 hq0 hq1 hδ hki hM1 hM2 hr
    _ _ _ hX hY hZ n

/-- The frame may be chosen separately at each physical point. Each K(t)
is a whole field in a frame held fixed while differentiating in y. -/
theorem tracePowerRoot_second_tendstoUniformlyOn_actual [CompleteSpace E]
    {α : Type*} {S : Set α} {U : Set E} (hU : IsOpen U)
    (K : α → E → Matrix ι ι ℂ) (x : α → E) (k : α → ι → ℝ) (i : ι)
    (hK : ∀ t ∈ S, ∀ l m, ContDiffOn ℝ 2 (fun y => K t y l m) U)
    (hx : ∀ t ∈ S, x t ∈ U)
    (hdiag : ∀ t ∈ S, K t (x t) = Matrix.diagonal (fun j => (k t j : ℂ)))
    (h0 : ∀ t ∈ S, ∀ j, 0 ≤ k t j) {q δ M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ)
    (hki : ∀ t ∈ S, δ ≤ k t i) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hr : ∀ t ∈ S, ∀ j, j ≠ i → k t j/k t i ≤ q)
    (htrace : ∀ t ∈ S, ∀ n : ℕ, ∀ y ∈ U, (K t y^(n+2)).trace.im = 0)
    (hspec : ∀ t ∈ S, ∀ᶠ y in 𝓝 (x t), ∀ z : ℂ,
      Module.End.HasEigenvalue (K t y).toLin' z → z.im = 0)
    (a b c d : E)
    (hX : ∀ t ∈ S, ∀ l m, ‖matrixDZ a b (K t) (x t) l m‖ ≤ M1)
    (hY : ∀ t ∈ S, ∀ l m, ‖matrixDZ c d (K t) (x t) l m‖ ≤ M1)
    (hZ : ∀ t ∈ S, ∀ j, ‖matrixDZ c d (matrixDZ a b (K t)) (x t) j j‖ ≤ M2) :
    TendstoUniformlyOn
      (fun n t => dz c d (dz a b (fun y => (tracePowerRoot (K t) (n+2) y : ℂ))) (x t))
      (fun t => dz c d (dz a b (fun y => (largestRealEigenvalue (K t y) : ℂ))) (x t)) atTop S := by
  have ht : Tendsto (fun n : ℕ =>
      traceRootSecondErrorConstant (Fintype.card ι) q δ M1 M2*((n : ℝ)+1)*q^n) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (geometric_polynomial_uniform_rate hq0 hq1).const_mul
        (traceRootSecondErrorConstant (Fintype.card ι) q δ M1 M2)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro t htS
  rw [dist_eq_norm, norm_sub_rev]
  exact (tracePowerRoot_second_uniform_error_actual hU (hK t htS) (hx t htS) (k t) i
    (hdiag t htS) (h0 t htS) hq0 hq1 hδ (hki t htS) hM1 hM2 (hr t htS)
    (htrace t htS) (hspec t htS) a b c d (hX t htS) (hY t htS) (hZ t htS) n).trans_lt hn

end PowerConvexity
