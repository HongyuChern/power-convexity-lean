import PowerConvexity.Calculus.ParallelNormalQuantitativeLower
import PowerConvexity.Calculus.UniformComplexTangentialLowerTwo

/-! # Uniform actual normal-derivative and paired-curvature constants.
Compactness is applied only on the fixed original boundary. No regularity
of a parameter-dependent defining function at t=0 is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem compact_regular_defining_normal_derivative_bound
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hDf : ∀ x ∈ K, fderiv ℝ f x ≠ 0) :
    ∃ M > 0, ∀ x ∈ K, ‖fderiv ℝ (definingUnitNormal f) x‖ ≤ M := by
  have hS : ContinuousOn (fun x => fderiv ℝ (definingUnitNormal f) x) K := by
    intro x hx
    have hn : ContDiffAt ℝ 2 (definingUnitNormal f) x :=
      definingUnitNormal_contDiffAt (hf.contDiffAt.of_le (by norm_num)) (hDf x hx)
    exact (hn.fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := (hK.image_of_continuousOn hS).isBounded.exists_norm_le
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (hM _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
local instance cnctRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cnctRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem compact_strictPsh_defining_normal_Levi_lower_two
    (e : Module.Basis (Fin 2) ℂ E) {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hDf : ∀ x ∈ K, fderiv ℝ f x ≠ 0)
    (hpsh : ∀ x ∈ K, (complexHessian e (fun j => Complex.I • e j) f x).PosDef) :
    ∃ ell > 0, ∀ x ∈ K, ∀ v : E,
      fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      ell*‖v‖^2 ≤ inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v+
        inner ℝ (fderiv ℝ (definingUnitNormal f) x (Complex.I • v)) (Complex.I • v) := by
  obtain ⟨eps,heps,hpaired⟩ := compact_strictPsh_paired_uniform_lower_two e hK hf hpsh
  have hDc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨G0,hG0⟩ := (hK.image hDc).isBounded.exists_norm_le
  let G := max G0 1
  have hG : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨eps/G,div_pos heps hG,?_⟩
  intro x hx v hv hIv
  have hgn : 0 < ‖gradient f x‖ := norm_pos_iff.mpr (definingGradient_ne_zero (hDf x hx))
  have hn : ‖gradient f x‖ ≤ G := by
    have he : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [he]
    exact (hG0 _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  rw [definingUnitNormal_fderiv_tangent_pair hf.contDiffAt (hDf x hx) v v hv,
    definingUnitNormal_fderiv_tangent_pair hf.contDiffAt (hDf x hx)
      (Complex.I • v) (Complex.I • v) hIv,← add_div]
  apply (le_div_iff₀ hgn).mpr
  calc
    (eps/G)*‖v‖^2*‖gradient f x‖ ≤ (eps/G)*‖v‖^2*G :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (div_nonneg heps.le hG.le) (sq_nonneg _))
    _ = eps*‖v‖^2 := by field_simp
    _ ≤ _ := hpaired x hx v

end PowerConvexity
