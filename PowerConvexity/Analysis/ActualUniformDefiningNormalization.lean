import PowerConvexity.Analysis.ActualCompactNormalizedDefiningGraphs
import Mathlib.Topology.MetricSpace.Thickening

/-! # Actual bounded inward defining-function normalizations

The normal and scalar are constructed from the actual pulled-back differential.
Their scalar bound is uniform on the compact true boundary and over all
linear equivalences with the displayed common inverse bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_compact_eventual_property_radius {K : Set E} (hK : IsCompact K)
    {Q : E → Prop} (hQ : ∀ c ∈ K, ∀ᶠ z in 𝓝 c, Q z) :
    ∃ r > 0, ∀ c ∈ K, ∀ z : E, ‖z-c‖ < r → Q z := by
  have hsub : K ⊆ interior {z | Q z} := fun c hc =>
    mem_interior_iff_mem_nhds.mpr (hQ c hc)
  obtain ⟨r,hr,hnear⟩ := hK.exists_thickening_subset_open isOpen_interior hsub
  refine ⟨r,hr,?_⟩
  intro c hc z hz
  apply interior_subset (hnear ?_)
  exact mem_thickening_iff.mpr ⟨c,hc,by simpa only [dist_eq_norm] using hz⟩

theorem actual_compact_inward_differential_normalization
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hDf : ∀ c ∈ K, fderiv ℝ f c ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ Z > 0, ∀ c ∈ K, ∀ G : E ≃L[ℝ] E,
      ‖G.symm.toContinuousLinearMap‖ ≤ B →
      ∃ N : E, ‖N‖=1 ∧ ∃ zeta : ℝ, zeta < 0 ∧ |zeta| ≤ Z ∧
        ∀ v : E, zeta*fderiv ℝ f c (G v)=inner ℝ N v := by
  have hdc : ContinuousOn (fun c => (‖fderiv ℝ f c‖)⁻¹) K :=
    (hf.continuous_fderiv (by norm_num)).norm.continuousOn.inv₀
      (fun c hc => norm_ne_zero_iff.mpr (hDf c hc))
  obtain ⟨M0,hM0⟩ := (hK.image_of_continuousOn hdc).isBounded.exists_norm_le
  let M := |M0|+1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hMinv (c : E) (hc : c ∈ K) : (‖fderiv ℝ f c‖)⁻¹ ≤ M := by
    have hh := hM0 _ (mem_image_of_mem _ hc)
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hh
    exact hh.trans (by dsimp only [M]; linarith [le_abs_self M0])
  refine ⟨B*M+1,by positivity,?_⟩
  intro c hc G hGi
  let D : E →L[ℝ] ℝ := fderiv ℝ f c
  let L : E →L[ℝ] ℝ := D.comp G.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro hz
    apply hDf c hc
    ext v
    have hh := congrArg (fun T : E →L[ℝ] ℝ => T (G.symm v)) hz
    simpa only [L,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      G.apply_symm_apply,ContinuousLinearMap.zero_apply,D] using hh
  let V := (InnerProductSpace.toDual ℝ E).symm L
  let d := ‖V‖
  have hdn : d=‖L‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map L
  have hd : 0 < d := by rw [hdn]; exact norm_pos_iff.mpr hL
  have hLv (v : E) : L v=inner ℝ V v := InnerProductSpace.toDual_symm_apply.symm
  have hDnorm : 0 < ‖D‖ := norm_pos_iff.mpr (hDf c hc)
  have hDL : ‖D‖ ≤ ‖L‖*B := by
    have he : D=L.comp G.symm.toContinuousLinearMap := by
      ext v
      simp only [L,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,G.apply_symm_apply]
    calc
      ‖D‖=‖L.comp G.symm.toContinuousLinearMap‖ := congrArg norm he
      _≤‖L‖*‖G.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _≤‖L‖*B := mul_le_mul_of_nonneg_left hGi (norm_nonneg _)
  have hdinv : d⁻¹ ≤ B*M := by
    have hfirst : d⁻¹ ≤ B*(‖D‖)⁻¹ := by
      have hh : 1 ≤ (B*d)/‖D‖ := (le_div_iff₀ hDnorm).mpr
        (by simpa only [one_mul,hdn,mul_comm] using hDL)
      have hh' : 1/d ≤ B*(‖D‖)⁻¹ := (div_le_iff₀ hd).mpr (by
        calc
          1 ≤ (B*d)/‖D‖ := hh
          _ = (B*(‖D‖)⁻¹)*d := by rw [div_eq_mul_inv]; ring)
      simpa only [one_div] using hh'
    exact hfirst.trans (mul_le_mul_of_nonneg_left (hMinv c hc) hB)
  let N := (-d⁻¹) • V
  have hN : ‖N‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hd)]
    exact inv_mul_cancel₀ hd.ne'
  refine ⟨N,hN,-d⁻¹,neg_neg_of_pos (inv_pos.mpr hd),?_,?_⟩
  · rw [abs_neg,abs_of_pos (inv_pos.mpr hd)]
    linarith
  · intro v
    change (-d⁻¹)*L v=inner ℝ ((-d⁻¹) • V) v
    rw [real_inner_smul_left,hLv]

end PowerConvexity
