import PowerConvexity.Calculus.SmallCMANormalizedCompactnessTwo
import PowerConvexity.Calculus.SmallCMAUniformLimitLocalTestsTwo

/-! # Actual compactness with a viscosity harmonic limit.
The same subsequence furnished by the equation-derived modulus has an
actual continuous limit satisfying both local Laplace test inequalities.
This theorem does not claim classical regularity of that limit.
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

theorem actual_small_CMA_normalized_sequence_has_viscosity_harmonic_limit_two
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
      IsViscosityHarmonicTwo g (ball 0 (1/2 : ℝ)) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformlyOn (fun n x => (ε (phi n))⁻¹*w (phi n) x) g atTop
          (closedBall 0 (1/2 : ℝ)) ∧
        ∀ x ∈ closedBall 0 (1/2 : ℝ), |g x| ≤ 1 := by
  classical
  obtain ⟨g,hgc,phi,hphi,hconv,hg1⟩ :=
    actual_small_CMA_normalized_sequence_has_uniform_subsequence_two w ε hε hε0 hwc hw hpsh hdet hbound
  let K := closedBall (0 : E) (1/2 : ℝ)
  let G : E → ℝ := fun x => if hx : x ∈ K then g ⟨x,hx⟩ else 0
  have heq (x : E) (hx : x ∈ K) : G x = g ⟨x,hx⟩ := by simp only [G,dif_pos hx]
  have hc : ContinuousOn G K := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hfun : (fun x : K => G x) = g := by funext x; exact heq x x.property
    change Continuous (fun x : K => G x)
    rw [hfun]
    exact hgc
  have hcv : TendstoUniformlyOn (fun n x => (ε (phi n))⁻¹*w (phi n) x) G atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) η hη] with n hn x hx
    rw [heq x hx]
    exact hn ⟨x,hx⟩
  have hsmall : ball (0 : E) (1/2 : ℝ) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hv : IsViscosityHarmonicTwo G (ball 0 (1/2 : ℝ)) :=
    actual_normalized_CMA_uniform_limit_is_viscosity_harmonic_two isOpen_ball
      (fun n => hε (phi n)) (hε0.comp hphi.tendsto_atTop)
      (fun n => (hw (phi n)).mono hsmall)
      (fun n x hx => hpsh (phi n) x (hsmall hx))
      (fun n x hx => hdet (phi n) x (hsmall hx))
      (hc.mono ball_subset_closedBall) (hcv.mono ball_subset_closedBall)
  refine ⟨G,hc,hv,phi,hphi,hcv,?_⟩
  intro x hx
  rw [heq x hx]
  simpa only [Real.norm_eq_abs] using hg1 ⟨x,hx⟩

end PowerConvexity
