import PowerConvexity.Calculus.SmallCMANormalizedViscosityCompactnessTwo
import PowerConvexity.Calculus.ViscosityHarmonicBallRegularityTwo

/-! # Actual classical harmonic limits of normalized small CMA solutions.
The original equation-derived subsequence and actual uniform limit are retained.
Classical regularity is a conclusion of the constructed harmonic replacement,
not an additional compactness hypothesis.
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

theorem actual_small_CMA_normalized_sequence_has_classical_harmonic_limit_two
    (w : ℕ → E → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hwc : ∀ n, ContinuousOn (w n) (closedBall 0 1))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) (ball 0 1))
    (hpsh : ∀ n x, x ∈ ball 0 1 →
      (1+complexHessian realDirections imagDirections (w n) x).PosSemidef)
    (hdet : ∀ n x, x ∈ ball 0 1 →
      (1+complexHessian realDirections imagDirections (w n) x).det = 1)
    (hbound : ∀ n x, x ∈ closedBall 0 1 → |w n x| ≤ ε n) :
    ∃ g : E → ℝ, ContinuousOn g (closedBall 0 (1/2 : ℝ)) ∧
      ContDiffOn ℝ 2 g (ball 0 (1/2 : ℝ)) ∧
      InnerProductSpace.HarmonicOnNhd g (ball 0 (1/2 : ℝ)) ∧
      IsViscosityHarmonicTwo g (ball 0 (1/2 : ℝ)) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformlyOn (fun n x => (ε (phi n))⁻¹*w (phi n) x) g atTop
          (closedBall 0 (1/2 : ℝ)) ∧
        ∀ x ∈ closedBall 0 (1/2 : ℝ), |g x| ≤ 1 := by
  obtain ⟨g,hgc,hgv,phi,hphi,hconv,hg1⟩ :=
    actual_small_CMA_normalized_sequence_has_viscosity_harmonic_limit_two
      w ε hε hε0 hwc hw hpsh hdet hbound
  exact ⟨g,hgc,hgv.contDiffOn_two isOpen_ball,hgv.classical_harmonic_two isOpen_ball,
    hgv,phi,hphi,hconv,hg1⟩

end PowerConvexity
