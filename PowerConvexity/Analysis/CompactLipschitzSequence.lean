import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Basic

/-! # Constructive subsequence interface for a bounded Lipschitz family.
The proof invokes the locked Arzela-Ascoli theorem with its compact-range and
common equicontinuity hypotheses explicitly checked.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
namespace PowerConvexity
variable {X F : Type*} [MetricSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [ProperSpace F]

theorem bounded_lipschitz_sequence_has_uniform_subsequence
    (f : ℕ → X → F) (C : NNReal)
    (hlip : ∀ n, LipschitzWith C (f n))
    (hbound : ∀ n x, ‖f n x‖ ≤ (C : ℝ)) :
    ∃ g : X → F, Continuous g ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n => f (phi n)) g atTop ∧
      LipschitzWith C g ∧ ∀ x, ‖g x‖ ≤ (C : ℝ) := by
  let k : ℕ → X →ᵇ F := fun n => BoundedContinuousFunction.mkOfCompact ⟨f n,(hlip n).continuous⟩
  have hcompactRange : ∀ (p : X →ᵇ F) (x : X), p ∈ range k → p x ∈ closedBall (0 : F) C := by
    rintro p x ⟨n,rfl⟩
    simpa only [k,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
      mem_closedBall,dist_zero_right] using hbound n x
  have hequi : Equicontinuous ((↑) : range k → X → F) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (C : ℝ)*r)
      (by
        have hc : Continuous (fun r : ℝ => (C : ℝ)*r) := continuous_const.mul continuous_id
        simpa only [mul_zero] using hc.tendsto (0 : ℝ))
    intro x y p
    rcases p with ⟨p,⟨n,rfl⟩⟩
    exact (hlip n).dist_le_mul x y
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) C)
    (isCompact_closedBall (0 : F) C) (range k) hcompactRange hequi
  obtain ⟨g,_,phi,hphi,hconv⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have huniform : TendstoUniformly (fun n => f (phi n)) (fun x => g x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  refine ⟨g,g.continuous,phi,hphi,huniform,?_,?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact le_of_tendsto ((huniform.tendsto_at x).dist (huniform.tendsto_at y))
      (Eventually.of_forall (fun n => (hlip (phi n)).dist_le_mul x y))
  · intro x
    exact le_of_tendsto (huniform.tendsto_at x).norm
      (Eventually.of_forall (fun n => hbound (phi n) x))

end PowerConvexity
