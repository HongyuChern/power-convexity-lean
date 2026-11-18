import PowerConvexity.Calculus.ActualFlatReflectionGeometryFour
import PowerConvexity.Calculus.ActualHarmonicBoundedComparisonFour
import PowerConvexity.Calculus.PoissonExtensionFour
import PowerConvexity.Calculus.PoissonIntegralSmoothFour

/-! # Actual odd reflection of a zero-boundary harmonic function on a half ball
The representative is constructed from the actual odd spherical trace by the
explicit Poisson integral. Comparison is applied on the genuine half ball,
including its flat disk. No boundary differentiability is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

theorem actual_zero_flat_harmonic_odd_reflection_four {N : E} (hN : ‖N‖=1)
    {u : E → ℝ} (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (huH : InnerProductSpace.HarmonicOnNhd u (actualFlatUpperBallFour N 1))
    (hu0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0) :
    ContinuousOn (actualFlatOddExtensionFour N u) (closedBall (0 : E) 1) ∧
    InnerProductSpace.HarmonicOnNhd (actualFlatOddExtensionFour N u) (ball (0 : E) 1) ∧
    ∀ k : ℕ∞ω, ContDiffOn ℝ k (actualFlatOddExtensionFour N u) (ball (0 : E) 1) := by
  let R := actualFlatReflectionFour N
  let v := actualFlatOddExtensionFour N u
  have hvC : ContinuousOn v (closedBall (0 : E) 1) :=
    actualFlatOddExtensionFour_continuousOn hN huC hu0
  let f : S → ℝ := fun xi => v xi
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp
    (hvC.mono sphere_subset_closedBall)
  let p := unitPoissonExtensionFour f
  have hpC : ContinuousOn p (closedBall (0 : E) 1) := unitPoissonExtensionFour_continuousOn_closedBall hf
  have hpH : InnerProductSpace.HarmonicOnNhd p (ball (0 : E) 1) := unitPoissonExtensionFour_harmonic hf
  have hpS (x : E) (hx : x ∈ sphere (0 : E) 1) : p x=v x :=
    unitPoissonExtensionFour_on_sphere f ⟨x,hx⟩
  have hRball (x : E) : R x ∈ ball (0 : E) 1 ↔ x ∈ ball (0 : E) 1 := by
    simp only [mem_ball,dist_zero_right,R.norm_map]
  have hRclosed (x : E) : R x ∈ closedBall (0 : E) 1 ↔ x ∈ closedBall (0 : E) 1 := by
    simp only [mem_closedBall,dist_zero_right,R.norm_map]
  have hRsphere (x : E) : R x ∈ sphere (0 : E) 1 ↔ x ∈ sphere (0 : E) 1 := by
    simp only [mem_sphere,dist_zero_right,R.norm_map]
  have hqC : ContinuousOn (fun x => -p (R x)) (closedBall (0 : E) 1) :=
    (hpC.comp R.continuous.continuousOn (fun x hx => (hRclosed x).mpr hx)).neg
  have hqH : InnerProductSpace.HarmonicOnNhd (fun x => -p (R x)) (ball (0 : E) 1) := by
    have hh := actual_harmonic_comp_linearIsometry_four R isOpen_ball hpH
    exact fun x hx => (hh x ((hRball x).mpr hx)).neg
  have hoddEq := actual_harmonic_bounded_uniqueness_four isOpen_ball
    (by rw [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]; exact isCompact_closedBall 0 1)
    (by simpa only [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] using hpC) hpH
    (by simpa only [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] using hqC) hqH (by
      intro x hx
      have hxS : x ∈ sphere (0 : E) 1 := by simpa only [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] using hx
      change p x = -p (R x)
      rw [hpS x hxS,hpS (R x) ((hRsphere x).mpr hxS)]
      have ho := actualFlatOddExtensionFour_odd hN u hu0 (sphere_subset_closedBall hxS)
      change v (R x) = -v x at ho
      rw [ho,neg_neg])
  have hpodd (x : E) (hx : x ∈ closedBall (0 : E) 1) : p (R x) = -p x := by
    have hh := hoddEq (by simpa only [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] using hx)
    change p x = -p (R x) at hh
    linarith
  have hpzero (x : E) (hx : x ∈ closedBall (0 : E) 1) (hz : inner ℝ N x=0) : p x=0 := by
    have hh := hpodd x hx
    rw [show R x=x from actualFlatReflectionFour_fixed hN hz] at hh
    linarith
  have hUo := actualFlatUpperBallFour_isOpen N 1
  have hUcl := actualFlatUpperBallFour_closure_subset N 1
  have hUK : IsCompact (closure (actualFlatUpperBallFour N 1)) :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_closure (fun x hx => (hUcl hx).1)
  have hup := actual_harmonic_bounded_uniqueness_four hUo hUK
    (huC.mono hUcl) huH (hpC.mono (fun x hx => (hUcl hx).1))
    (hpH.mono inter_subset_left) (by
      intro x hx
      obtain ⟨hc,hs|hz⟩ := actualFlatUpperBallFour_frontier_subset N 1 hx
      · rw [hpS x hs]
        exact (actualFlatOddExtensionFour_upper N u hc.2).symm
      · rw [hu0 x hc.1 hz,hpzero x hc.1 hz])
  have hupeq (x : E) (hx : x ∈ actualFlatClosedUpperBallFour N 1) : u x=p x := by
    by_cases hs : x ∈ sphere (0 : E) 1
    · rw [hpS x hs]
      exact (actualFlatOddExtensionFour_upper N u hx.2).symm
    by_cases hz : inner ℝ N x=0
    · rw [hu0 x hx.1 hz,hpzero x hx.1 hz]
    have hxb : x ∈ ball (0 : E) 1 := by
      exact mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hx.1) (fun he => hs (mem_sphere.mpr he)))
    have hxn : 0 < inner ℝ N x := lt_of_le_of_ne hx.2 (Ne.symm hz)
    exact hup (subset_closure ⟨hxb,hxn⟩)
  have hEq : EqOn v p (closedBall (0 : E) 1) := by
    intro x hx
    by_cases hxn : 0 ≤ inner ℝ N x
    · rw [show v x=u x from actualFlatOddExtensionFour_upper N u hxn]
      exact hupeq x ⟨hx,hxn⟩
    · have hn : 0 ≤ inner ℝ N (R x) := by
        rw [actualFlatReflectionFour_normal hN]
        linarith
      change (if 0 ≤ inner ℝ N x then u x else -u (R x))=p x
      rw [if_neg hxn,hupeq (R x) ⟨(hRclosed x).mpr hx,hn⟩,hpodd x hx,neg_neg]
  have hnear (x : E) (hx : x ∈ ball (0 : E) 1) : v =ᶠ[𝓝 x] p := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hEq (ball_subset_closedBall hy)
  refine ⟨hvC,fun x hx => (InnerProductSpace.harmonicAt_congr_nhds (hnear x hx)).mpr (hpH x hx),?_⟩
  intro k x hx
  have hpnear : p =ᶠ[𝓝 x] poissonIntegralFour unitSphereProbabilityFour f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact unitPoissonExtensionFour_on_ball f hy
  exact ((poissonIntegralFour_contDiffAt unitSphereProbabilityFour hf hx k).congr_of_eventuallyEq
    ((hnear x hx).trans hpnear)).contDiffWithinAt

end PowerConvexity
