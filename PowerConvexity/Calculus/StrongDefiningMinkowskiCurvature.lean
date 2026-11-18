import PowerConvexity.Calculus.CompactNormalCoefficientsTwo
import PowerConvexity.Calculus.StrongConvexDomainApproximation

/-! # Uniform genuine Minkowski curvature from a strongly convex defining function

The positive lower bound is for the actual derivative of the unit normal,
equivalently the actual tangent Hessian of any regular local defining function
divided by its gradient norm.  The same constant works for every positive
Minkowski parameter, including the endpoint one.  It depends on the fixed
strongly convex domain and may degenerate along its outer approximations.

Only previously proved parallel-normal transport is used.  No positive
curvature is attributed to a domain merely from strict boundary chords.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem minkowski_frontier_exists_parallel_global_defining
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hb : ∀ x ∈ frontier U, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ x ∈ frontier U, y = definingParallelMap F t ((1-t)*R) x := by
  by_cases htlt : t < 1
  · have hboundary : HasC2LocalDefiningFunction U :=
      fun x hx => ⟨F,hF.contDiffAt,(hb x hx).1,(hb x hx).2.1,(hb x hx).2.2⟩
    obtain ⟨x,hx,f,hf,hfx,hDf,hdef,hyf⟩ := minkowski_frontier_exists_parallel_normal
      hU hconv hK hboundary ht htlt hR hy
    have hs : ∀ z ∈ closure U, inner ℝ (definingUnitNormal f x) (z-x) ≤ 0 := by
      change closure U ⊆ {z : E | inner ℝ (definingUnitNormal f x) (z-x) ≤ 0}
      exact closure_minimal
        (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
          (hf.differentiableAt (by norm_num)) hfx hdef)
        (isClosed_le (show Continuous (fun z : E => inner ℝ (definingUnitNormal f x) (z-x)) by
          fun_prop) continuous_const)
    have hn := supporting_unit_vector_eq_definingUnitNormal hF.contDiffAt
      (hb x hx).1 (hb x hx).2.1 (hb x hx).2.2 (definingUnitNormal_norm hDf) hs
    exact ⟨x,hx,by simpa only [definingParallelMap,hn] using hyf⟩
  · have htEq : t = 1 := le_antisymm ht1 (not_lt.mp htlt)
    subst t
    have hBn : (ball (0 : E) R).Nonempty := ⟨0,mem_ball_self hR⟩
    rw [minkowskiDomain_one hBn] at hy
    exact ⟨y,hy,by simp only [definingParallelMap,sub_self,zero_mul,zero_smul,one_smul,add_zero]⟩

theorem compact_strong_defining_normal_tangent_lower
    {K : Set E} (hK : IsCompact K) {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hDf : ∀ x ∈ K, fderiv ℝ F x ≠ 0) {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ K, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v) :
    ∃ ell > 0, ∀ x ∈ K, ∀ v : E, fderiv ℝ F x v = 0 →
      ell*‖v‖^2 ≤ inner ℝ (fderiv ℝ (definingUnitNormal F) x v) v := by
  have hDc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  obtain ⟨G0,hG0⟩ := (hK.image hDc).isBounded.exists_norm_le
  let G := max G0 1
  have hG : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨(2*delta)/G,div_pos (mul_pos (by norm_num) hdelta) hG,?_⟩
  intro x hx v hv
  have hgn : 0 < ‖gradient F x‖ := norm_pos_iff.mpr (definingGradient_ne_zero (hDf x hx))
  have hn : ‖gradient F x‖ ≤ G := by
    have he : ‖gradient F x‖ = ‖fderiv ℝ F x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [he]
    exact (hG0 _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  rw [definingUnitNormal_fderiv_tangent_pair hF.contDiffAt (hDf x hx) v v hv]
  apply (le_div_iff₀ hgn).mpr
  calc
    ((2*delta)/G)*‖v‖^2*‖gradient F x‖ ≤ ((2*delta)/G)*‖v‖^2*G :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2*delta*‖v‖^2 := by field_simp
    _ ≤ _ := hH x hx v

theorem strong_defining_minkowski_actual_tangent_curvature_uniform_lower
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {F : E → ℝ} (hF : ContDiff ℝ 3 F)
    (hb : ∀ x ∈ frontier U, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v)
    {R : ℝ} (hR : 0 < R) :
    ∃ kappa > 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), ∀ g : E → ℝ,
        ContDiffAt ℝ 2 g y → g y = 0 → fderiv ℝ g y ≠ 0 →
        (∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) →
        ∀ v : E, fderiv ℝ g y v = 0 →
          kappa*‖v‖^2 ≤ realHessian g y v v/‖gradient g y‖ := by
  have hFK : IsCompact (frontier U) :=
    hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  obtain ⟨M,hM,hMS⟩ := compact_regular_defining_normal_derivative_bound hFK hF
    (fun x hx => (hb x hx).2.1)
  obtain ⟨ell,hell,hold⟩ := compact_strong_defining_normal_tangent_lower hFK hF2
    (fun x hx => (hb x hx).2.1) hdelta hH
  have hden : 0 < 1+R*M := by positivity
  refine ⟨ell/(1+R*M),div_pos hell hden,?_⟩
  intro t ht ht1 y hy g hg hgy hDg hgdef v hv
  obtain ⟨x,hx,rfl⟩ := minkowski_frontier_exists_parallel_global_defining hU hconv hK hF2 hb
    ht ht1 hR hy
  have hvtan := (parallel_defining_tangent_kernel_iff hU hconv hx hF2.contDiffAt
    (hb x hx).1 (hb x hx).2.1 (hb x hx).2.2 ht.le ht1 hg hgy hDg hgdef v).mp hv
  have hl := hold x hx v hvtan
  have hh := parallel_defining_normal_tangent_quantitative_lower hU hconv hx hF2.contDiffAt
    (hb x hx).1 (hb x hx).2.1 (hb x hx).2.2 hM (hMS x hx)
    ht ht1 hR hg hgy hDg hgdef hv
  rw [definingUnitNormal_fderiv_tangent_pair hg hDg v v hv] at hh
  have hl' := div_le_div_of_nonneg_right hl hden.le
  have he : ell*‖v‖^2/(1+R*M) = (ell/(1+R*M))*‖v‖^2 := by ring
  rw [he] at hl'
  exact hl'.trans hh

end PowerConvexity
