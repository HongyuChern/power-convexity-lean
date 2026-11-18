import PowerConvexity.Analysis.QuadraticPerturbationPaths
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Exact first-order contact of Appendix A's curved and linear paths -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem linearPerturbationPath_hasDerivAt_zero (q h : P) :
    HasDerivAt (fun t : ℝ => q+t • h) h 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add q

theorem curvedPerturbationPath_hasDerivAt_zero (q h : P) (γ : ℝ) :
    HasDerivAt (curvedPerturbationPath q h γ) h 0 := by
  have ha : HasDerivAt (fun t : ℝ => 1-γ*t^2) 0 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul γ) using 1 <;> try rfl
    all_goals norm_num [id_eq]
  convert (ha.smul_const q).add ((hasDerivAt_id (0:ℝ)).smul_const h) using 1 <;> try rfl
  all_goals simp [curvedPerturbationPath]

/-- Only the outer function is differentiated at the base point.  No
smoothness of the minimum eigenvalue at a repeated root is asserted. -/
theorem curvedPerturbationPath_comp_hasDerivAt {f : P → ℝ} {q h : P} {c : ℝ}
    (hf : DifferentiableAt ℝ f q)
    (hlin : HasDerivAt (fun t : ℝ => f (q+t • h)) c 0) (γ : ℝ) :
    HasDerivAt (fun t => f (curvedPerturbationPath q h γ t)) c 0 := by
  have hl : HasFDerivAt f (fderiv ℝ f q) (q+(0:ℝ) • h) := by simpa using hf.hasFDerivAt
  have hc : HasFDerivAt f (fderiv ℝ f q) (curvedPerturbationPath q h γ 0) := by
    simpa [curvedPerturbationPath] using hf.hasFDerivAt
  have hd : fderiv ℝ f q h = c :=
    (hl.comp_hasDerivAt 0 (linearPerturbationPath_hasDerivAt_zero q h)).unique hlin
  have hh := hc.comp_hasDerivAt 0 (curvedPerturbationPath_hasDerivAt_zero q h γ)
  rw [hd] at hh
  convert hh using 1 <;> rfl

theorem hasDerivAt_negative_right_decrease {f : ℝ → ℝ} {c : ℝ}
    (hf : HasDerivAt f c 0) (hc : c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → f t < f 0 := by
  have hs : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹*(f t-f 0) < 0 := by
    simpa only [zero_add,smul_eq_mul] using hf.tendsto_slope_zero_right.eventually (gt_mem_nhds hc)
  have hn := eventually_nhdsWithin_iff.mp hs
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ
  have hb : t ∈ ball (0:ℝ) δ := by
    simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht] using htδ
  have hneg := hball hb ht
  apply sub_neg.mp
  by_contra h
  have hh := mul_nonneg (inv_pos.mpr ht).le (le_of_not_gt h)
  linarith

theorem hasDerivAt_positive_left_decrease {f : ℝ → ℝ} {c : ℝ}
    (hf : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, -δ < t → t < 0 → f t < f 0 := by
  have hs : ∀ᶠ t in 𝓝[<] (0:ℝ), 0 < t⁻¹*(f t-f 0) := by
    simpa only [zero_add,smul_eq_mul] using hf.tendsto_slope_zero_left.eventually (lt_mem_nhds hc)
  have hn := eventually_nhdsWithin_iff.mp hs
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,?_⟩
  intro t htδ ht
  have hb : t ∈ ball (0:ℝ) δ := by
    simp only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_neg ht]
    linarith
  have hpos := hball hb ht
  have hi : t⁻¹ < 0 := inv_lt_zero.mpr ht
  have hn : f t-f 0 < 0 := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg hi.le (le_of_not_gt h)
    linarith
  exact sub_neg.mp hn

end PowerConvexity
