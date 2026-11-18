import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The true sign on a normal line from the actual normalized defining differential -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_normal_line_sign {N : E} (hN : ‖N‖=1) {f : E → ℝ}
    (hf : ContDiffAt ℝ 1 f 0) (hDN : fderiv ℝ f 0 N=1) :
    ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, ∀ t : ℝ, y-z=t • N → f z=0 →
        (0 < f y ↔ 0 < t) ∧ (f y=0 ↔ t=0) ∧ (f y < 0 ↔ t < 0) := by
  have hsmall := (hf.hasStrictFDerivAt (by norm_num)).isLittleO.bound (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨V,hVo,h0,hVV⟩ := exists_nhds_square hsmall
  refine ⟨V,hVo,h0,?_⟩
  intro y hy z hz t hdiff hfz
  have hh := hVV (show (y,z) ∈ V ×ˢ V from ⟨hy,hz⟩)
  change |f y-f z-fderiv ℝ f 0 (y-z)| ≤ (1/2 : ℝ)*‖y-z‖ at hh
  have herror : |f y-t| ≤ (1/2 : ℝ)*|t| := by
    simpa only [hdiff,hfz,sub_zero,map_smul,hDN,smul_eq_mul,mul_one,Real.norm_eq_abs,
      norm_smul,hN,mul_one] using hh
  have hlow := (abs_le.mp herror).1
  have hhigh := (abs_le.mp herror).2
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro hypos
      by_contra ht
      have htn : t ≤ 0 := le_of_not_gt ht
      rw [abs_of_nonpos htn] at hhigh
      linarith
    · intro ht
      rw [abs_of_pos ht] at hlow
      linarith
  · constructor
    · intro hyzero
      rw [hyzero,zero_sub,abs_neg] at herror
      have hzabs : |t|=0 := by linarith [abs_nonneg t]
      exact abs_eq_zero.mp hzabs
    · intro ht
      subst t
      have hh : |f y| ≤ 0 := by simpa only [sub_zero,abs_zero,mul_zero] using herror
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  · constructor
    · intro hyneg
      by_contra ht
      have htn : 0 ≤ t := le_of_not_gt ht
      rw [abs_of_nonneg htn] at hlow
      linarith
    · intro ht
      rw [abs_of_neg ht] at hhigh
      linarith

end PowerConvexity
