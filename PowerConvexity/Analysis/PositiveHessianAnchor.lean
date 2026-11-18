import PowerConvexity.Calculus.ScalarInteriorRegularity
import CHS.Calculus.AffinePullback

/-! # A positive Hessian point from a negative function with zero boundary data -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem realHessian_norm_sub_sq (c x : E) :
    realHessian (fun y : E => ‖y-c‖^2) x = (2 : ℝ) • (realInnerForm (E := E)) := by
  have he : (fun y : E => ‖y-c‖^2) =
      fun y => ‖-c + (ContinuousLinearMap.id ℝ E) y‖^2 := by
    funext y
    simp only [ContinuousLinearMap.id_apply, sub_eq_add_neg, add_comm]
  rw [he]
  ext v w
  rw [realHessian_comp_affine (ContinuousLinearMap.id ℝ E) (-c)
    (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt]
  rw [realHessian_norm_sq]
  rfl

/-- This produces a genuine strictly positive real Hessian at one interior
point. It does not use a positive boundary curvature assumption. -/
theorem exists_positive_realHessian_of_negative_zero_boundary
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) {f : E → ℝ}
    (hfc : ContinuousOn f (closure U)) (hf : ContDiffOn ℝ 2 f U)
    (hboundary : ∀ x ∈ frontier U, f x = 0) (hnegative : ∃ c ∈ U, f c < 0) :
    ∃ x ∈ U, ∀ v : E, v ≠ 0 → 0 < realHessian f x v v := by
  obtain ⟨c, hc, hfcneg⟩ := hnegative
  have hcK : c ∈ closure U := subset_closure hc
  have hq : ContDiff ℝ 2 (fun y : E => ‖y-c‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)
  obtain ⟨z, hz, hzmax⟩ := hK.exists_isMaxOn ⟨c, hcK⟩ hq.continuous.continuousOn
  let M := ‖z-c‖^2
  have hM : 0 ≤ M := sq_nonneg _
  let ε := -f c / (2 * (M+1))
  have hden : 0 < 2 * (M+1) := by positivity
  have hε : 0 < ε := div_pos (neg_pos.mpr hfcneg) hden
  have hεeq : ε * (2 * (M+1)) = -f c := by dsimp only [ε]; field_simp
  have hεM : ε * M < -f c := by
    have hp : 0 < ε * (M+2) := by positivity
    nlinarith
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn ⟨c, hcK⟩
    (hfc.sub ((continuousOn_const (c := ε)).mul hq.continuous.continuousOn))
  have hxvalue : f x - ε * ‖x-c‖^2 ≤ f c := by
    have h := hmin hcK
    change f x - ε * ‖x-c‖^2 ≤ f c - ε * ‖c-c‖^2 at h
    simpa using h
  have hxU : x ∈ U := by
    by_contra hxout
    have hxfront : x ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hxK, hxout⟩
    have hb := hboundary x hxfront
    have hmax : ‖x-c‖^2 ≤ M := hzmax hxK
    have hbound := mul_le_mul_of_nonneg_left hmax hε.le
    linarith
  have hm : IsLocalMin (fun y => f y - ε * ‖y-c‖^2) x :=
    hmin.isLocalMin (Filter.mem_of_superset (hU.mem_nhds hxU) subset_closure)
  refine ⟨x, hxU, ?_⟩
  intro v hv
  have hfx := hf.contDiffAt (hU.mem_nhds hxU)
  have hH := realHessian_le_of_isLocalMin_sub hfx
    (contDiffAt_const.mul hq.contDiffAt) hm v
  rw [realHessian_const_mul_at hq.contDiffAt, realHessian_norm_sub_sq] at hH
  change ε * (2 * inner ℝ v v) ≤ realHessian f x v v at hH
  rw [real_inner_self_eq_norm_sq] at hH
  have hp : 0 < ε * (2 * ‖v‖^2) := by
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  exact hp.trans_le hH

end PowerConvexity
