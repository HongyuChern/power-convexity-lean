import PowerConvexity.Analysis.CompactLipschitzSequence
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Actual compactness from a common tail modulus.
The finitely many early functions are controlled by their actual
continuity. Thus asymptotic control gives equicontinuity of the full
sequence before the locked Arzela-Ascoli theorem is invoked.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
namespace PowerConvexity
variable {X F : Type*} [MetricSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [ProperSpace F]

theorem continuous_sequence_equicontinuous_of_tail_modulus
    (f : ℕ → X → F) (hf : ∀ n, Continuous (f n))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n in atTop, ∀ x y : X, dist x y < δ → dist (f n x) (f n y) < ε) :
    Equicontinuous f := by
  intro x₀
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  obtain ⟨δ,hδ,ht⟩ := htail ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 ht
  have hsingle (n : ℕ) : ∀ᶠ x in 𝓝 x₀, dist (f n x₀) (f n x) < ε := by
    have hh : Tendsto (fun x => dist (f n x₀) (f n x)) (𝓝 x₀) (𝓝 0) := by
      simpa only [dist_self] using
        ((continuous_const : Continuous (fun _ : X => f n x₀)).dist (hf n)).tendsto x₀
    exact hh (Iio_mem_nhds hε)
  have hfinite : ∀ M : ℕ, ∀ᶠ x in 𝓝 x₀, ∀ n < M, dist (f n x₀) (f n x) < ε := by
    intro M
    induction M with
    | zero => exact Eventually.of_forall (fun _ n hn => (Nat.not_lt_zero n hn).elim)
    | succ M ih =>
      filter_upwards [ih,hsingle M] with x hx hxM n hn
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hlt | heq
      · exact hx n hlt
      · simpa only [heq] using hxM
  filter_upwards [Metric.ball_mem_nhds x₀ hδ,hfinite N] with x hx hfin n
  by_cases hn : n < N
  · exact hfin n hn
  · exact hN n (Nat.le_of_not_gt hn) x₀ x (by simpa only [mem_ball,dist_comm] using hx)

theorem bounded_continuous_sequence_has_uniform_subsequence_of_tail_modulus
    (f : ℕ → X → F) (hf : ∀ n, Continuous (f n)) (C : ℝ)
    (hbound : ∀ n x, ‖f n x‖ ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n in atTop, ∀ x y : X, dist x y < δ → dist (f n x) (f n y) < ε) :
    ∃ g : X → F, Continuous g ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n => f (phi n)) g atTop ∧ ∀ x, ‖g x‖ ≤ C := by
  let k : ℕ → X →ᵇ F := fun n => BoundedContinuousFunction.mkOfCompact ⟨f n,hf n⟩
  have he := continuous_sequence_equicontinuous_of_tail_modulus f hf htail
  have hcompactRange : ∀ (p : X →ᵇ F) (x : X), p ∈ range k → p x ∈ closedBall (0 : F) C := by
    rintro p x ⟨n,rfl⟩
    simpa only [k,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
      mem_closedBall,dist_zero_right] using hbound n x
  have hequi : Equicontinuous ((↑) : range k → X → F) := by
    intro x₀
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.mp (he x₀)) ε hε] with x hx p
    rcases p with ⟨p,⟨n,rfl⟩⟩
    exact hx n
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) C)
    (isCompact_closedBall (0 : F) C) (range k) hcompactRange hequi
  obtain ⟨g,_,phi,hphi,hconv⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have huniform : TendstoUniformly (fun n => f (phi n)) (fun x => g x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  refine ⟨g,g.continuous,phi,hphi,huniform,?_⟩
  intro x
  exact le_of_tendsto (huniform.tendsto_at x).norm
    (Eventually.of_forall (fun n => hbound (phi n) x))

end PowerConvexity
