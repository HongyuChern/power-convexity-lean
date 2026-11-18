import PowerConvexity.Calculus.SmallCMAAsymptoticModulusTwo
import PowerConvexity.Analysis.AsymptoticEquicontinuity

/-! # Actual uniform compactness of normalized small CMA deviations.
The asymptotic modulus is derived from the equation and the actual
amplitude bound. No equicontinuity or derivative bound is a premise.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_small_CMA_normalized_sequence_has_uniform_subsequence_two
    (w : ℕ → E → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hwc : ∀ n, ContinuousOn (w n) (closedBall 0 1))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) (ball 0 1))
    (hpsh : ∀ n x, x ∈ ball 0 1 →
      (1+complexHessian realDirections imagDirections (w n) x).PosSemidef)
    (hdet : ∀ n x, x ∈ ball 0 1 →
      (1+complexHessian realDirections imagDirections (w n) x).det = 1)
    (hbound : ∀ n x, x ∈ closedBall 0 1 → |w n x| ≤ ε n) :
    ∃ g : (closedBall (0 : E) (1/2 : ℝ)) → ℝ, Continuous g ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformly (fun n (x : closedBall (0 : E) (1/2 : ℝ)) =>
          (ε (phi n))⁻¹*w (phi n) x) g atTop ∧ ∀ x, ‖g x‖ ≤ 1 := by
  let K := closedBall (0 : E) (1/2 : ℝ)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let f : ℕ → K → ℝ := fun n x => (ε n)⁻¹*w n x
  have hK : K ⊆ closedBall (0 : E) 1 := closedBall_subset_closedBall (by norm_num)
  have hf (n : ℕ) : Continuous (f n) := by
    have hc : Continuous (fun x : K => w n x) :=
      continuousOn_iff_continuous_restrict.mp ((hwc n).mono hK)
    exact continuous_const.mul hc
  have hb (n : ℕ) (x : K) : ‖f n x‖ ≤ 1 := by
    change ‖(ε n)⁻¹*w n x‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (inv_pos.mpr (hε n))]
    exact (inv_mul_le_iff₀ (hε n)).mpr (by simpa only [mul_one] using hbound n x (hK x.property))
  apply bounded_continuous_sequence_has_uniform_subsequence_of_tail_modulus f hf 1 hb
  intro η hη
  obtain ⟨δ,hδ,_hδle,hmod⟩ := small_CMA_normalized_asymptotic_modulus_two (half_pos hη)
  refine ⟨δ,hδ,?_⟩
  have hsmall : ∀ᶠ n in atTop, ε n < δ^2/2 :=
    hε0 (Iio_mem_nhds (by positivity : (0 : ℝ) < δ^2/2))
  filter_upwards [hsmall] with n hn x y hxy
  have hd := hmod (w n) (ε n) (hε n).le hn.le (hwc n) (hw n) (hpsh n) (hdet n)
    (hbound n) x x.property y y.property hxy.le
  have hi : 0 < (ε n)⁻¹ := inv_pos.mpr (hε n)
  have heq : dist (f n x) (f n y) = (ε n)⁻¹*|w n x-w n y| := by
    rw [Real.dist_eq]
    change |(ε n)⁻¹*w n x-(ε n)⁻¹*w n y| = _
    rw [← mul_sub,abs_mul,abs_of_pos hi]
  rw [heq]
  calc
    (ε n)⁻¹*|w n x-w n y| ≤ (ε n)⁻¹*((η/2)*ε n) :=
      mul_le_mul_of_nonneg_left hd hi.le
    _ = η/2 := by field_simp [(hε n).ne'] <;> ring
    _ < η := half_lt_self hη

end PowerConvexity
