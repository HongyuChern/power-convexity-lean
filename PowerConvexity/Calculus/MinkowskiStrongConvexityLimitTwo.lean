import PowerConvexity.Calculus.StrongConvexityLimits
import PowerConvexity.Calculus.MinkowskiFamilyUniformContinuityTwo

/-! # The quantitative strictness limit along an actual Minkowski Dirichlet family

Classical family existence remains explicit data. This theorem supplies the
valid limiting inference at TeX 1173; it is not a construction of that family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
  (hA : Convex ℝ A) (hB : Convex ℝ B)
  {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
  (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
  (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
  (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
  (u : Icc (0:ℝ) 1 → E → ℝ)
  (huc : ∀ t : Icc (0:ℝ) 1, ContinuousOn (u t) (closure (minkowskiDomain t A B)))
  (hu : ∀ t : Icc (0:ℝ) 1, ContDiffOn ℝ 2 (u t) (minkowskiDomain t A B))
  (hAu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
    (complexHessian a b (u t) x).PosDef)
  (hdu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
    (complexHessian a b (u t) x).det = 1)
  (hbu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ frontier (minkowskiDomain t A B), u t x = 0)
include hAo hBo hA hB hρ hL hballA hballB hAb hBb a b hab u huc hu hAu hdu hbu


/-- The limit step at TeX 1173, for an already supplied classical family.
Only value continuity is needed once the uniform positive margin has been proved. -/
theorem minkowski_classicalDirichlet_strongConvexity_limit_two
    {α : Type*} {l : Filter α} [NeBot l]
    {s : Icc (0:ℝ) 1} {t : α → Icc (0:ℝ) 1} (ht : Tendsto t l (𝓝 s))
    {C : ℝ} (hC : 0 < C)
    (hstrong : ∀ᶠ q in l, StrongConvexOn (minkowskiDomain (t q) A B) C (powerTransform (u (t q)))) :
    StrongConvexOn (minkowskiDomain s A B) C (powerTransform (u s)) ∧
      StrictConvexOn ℝ (minkowskiDomain s A B) (powerTransform (u s)) := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hV := minkowskiDomain_isOpen hAo hBo hAn (s:ℝ)
  have hmem (x : E) (hx : x ∈ minkowskiDomain s A B) :
      ∀ᶠ q in l, x ∈ minkowskiDomain (t q) A B := by
    have hh := minkowskiDomain_compact_eventually_subset hA hB hρ hL hballA hballB hAb hBb hV
      (isCompact_singleton : IsCompact ({x}:Set E)) (by simpa using hx)
    filter_upwards [ht.eventually hh] with q hq
    exact hq (mem_singleton x)
  have hc := minkowski_classicalDirichlet_joint_continuous_from_endpoint_geometry_two
    hAo hBo hA hB hρ hL hballA hballB hAb hBb a b hab u huc hu hAu hdu hbu
  apply powerTransform_strictConvexOn_varying_limit (minkowskiDomain_convex hA hB (s:ℝ))
    hC hmem hstrong
  intro x hx
  have hpair : Tendsto (fun q => (t q,x)) l (𝓝 (s,x)) := ht.prodMk_nhds tendsto_const_nhds
  have hh := (hc.tendsto (s,x)).comp hpair
  have he : (fun q => (minkowskiDomain (t q) A B).indicator (u (t q)) x) =ᶠ[l]
      (fun q => u (t q) x) := by
    filter_upwards [hmem x hx] with q hq
    exact indicator_of_mem hq _
  have hh' := hh.congr' he
  simpa only [Function.comp_def, indicator_of_mem hx] using hh'

end PowerConvexity
