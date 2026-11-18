import PowerConvexity.Calculus.ParameterGraphLocalInverse

/-! # Joint local inverses of the actual Minkowski normal map

The parameter is part of the actual inverse-function problem.  Smoothness
is derived from the original boundary defining function, and injectivity
from its nonnegative real tangent curvature.  Positive real curvature is
not assumed.  The base parameter is strictly positive.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem definingMinkowskiParallelMap_joint_contDiffAt
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hDf : fderiv ℝ f x ≠ 0) (s R : ℝ) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => definingParallelMap f p.1 ((1-p.1)*R) p.2) (s,x) := by
  have hnormal : ContDiffAt ℝ ∞
      (fun p : ℝ × E => definingUnitNormal f p.2) (s,x) :=
    (definingUnitNormal_contDiffAt (n := ∞) (by simpa using hf) hDf).comp
      (s,x) contDiffAt_snd
  have hscalar : ContDiffAt ℝ ∞ (fun p : ℝ × E => (1-p.1)*R) (s,x) := by
    fun_prop
  exact (contDiffAt_fst.smul contDiffAt_snd).add (hscalar.smul hnormal)

theorem definingMinkowskiParallelMap_exists_joint_smooth_localInverse_of_convex
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 ≤ R) :
    ∃ g : ℝ × E → E,
      ContDiffAt ℝ ∞ g (s,definingParallelMap f s ((1-s)*R) x) ∧
      g (s,definingParallelMap f s ((1-s)*R) x) = x ∧
      (∀ᶠ p in 𝓝 (s,definingParallelMap f s ((1-s)*R) x),
        definingParallelMap f p.1 ((1-p.1)*R) (g p) = p.2) ∧
      (∀ᶠ p in 𝓝 (s,x),
        g (p.1,definingParallelMap f p.1 ((1-p.1)*R) p.2) = p.2) := by
  apply exists_parameter_preserving_smooth_localInverse
    (definingMinkowskiParallelMap_joint_contDiffAt hf hDf s R)
  exact definingParallelMap_fderiv_injective_of_convex hU hconv hx
    ((contDiffAt_infty.mp hf) 2) hfx hDf hdef hs
    (mul_nonneg (sub_nonneg.mpr hs1) hR)

end PowerConvexity
