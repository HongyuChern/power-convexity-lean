import PowerConvexity.Analysis.EnvelopeOn
import Mathlib.Topology.Order.IntermediateValue

/-! # Boundary anchors and the first zero in a continuous deformation -/

set_option autoImplicit false
open Set
namespace PowerConvexity

/-- Positivity at one closure point already supplies an interior anchor. -/
theorem exists_positive_anchor_of_closure {X : Type*} [TopologicalSpace X]
    {U : Set X} {w : X → ℝ} (hw : ContinuousOn w (closure U))
    {p : X} (hp : p ∈ closure U) (hwp : 0 < w p) :
    ∃ x ∈ U, 0 < w x := by
  by_contra h
  have hle : ∀ x ∈ U, w x ≤ 0 := by
    intro x hx
    exact le_of_not_gt (fun hp => h ⟨x, hx, hp⟩)
  have hp0 : w p ≤ 0 := le_on_closure hle hw continuousOn_const hp
  exact (not_lt_of_ge hp0) hwp

/-- The first contact is positive in parameter time, and every preceding
parameter has a strictly positive minimum. -/
theorem exists_first_zero_on_unitInterval {m : ℝ → ℝ}
    (hm : ContinuousOn m (Icc 0 1)) (h0 : 0 < m 0) (h1 : m 1 ≤ 0) :
    ∃ t₀ ∈ Ioc (0 : ℝ) 1, m t₀ = 0 ∧
      (∀ t ∈ Ico (0 : ℝ) t₀, 0 < m t) := by
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hm
    (show (0 : ℝ) ∈ Icc (m 1) (m 0) from ⟨h1, h0.le⟩)
  let Z : Set ℝ := Icc 0 1 ∩ m ⁻¹' ({0} : Set ℝ)
  have hZclosed : IsClosed Z :=
    hm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZ : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed (fun _ hz => hz.1)
  have hZne : Z.Nonempty := ⟨s, hs, hsz⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hZ.exists_isMinOn hZne continuous_id.continuousOn
  have ht0 : 0 < t₀ := by
    have ht0n : t₀ ≠ 0 := by
      intro he
      have hz : m 0 = 0 := he ▸ ht₀.2
      linarith
    exact lt_of_le_of_ne ht₀.1.1 (Ne.symm ht0n)
  refine ⟨t₀, ⟨ht0, ht₀.1.2⟩, ht₀.2, ?_⟩
  intro t ht
  by_contra htp
  have ht1 : t ≤ 1 := ht.2.le.trans ht₀.1.2
  obtain ⟨r, hr, hrz⟩ := intermediate_value_Icc' ht.1
    (hm.mono (Icc_subset_Icc le_rfl ht1))
    (show (0 : ℝ) ∈ Icc (m t) (m 0) from ⟨le_of_not_gt htp, h0.le⟩)
  have hrZ : r ∈ Z := ⟨⟨hr.1, hr.2.trans ht1⟩, hrz⟩
  have htr : t₀ ≤ r := hmin hrZ
  linarith [hr.2, ht.2]

/-- A continuous minimum cannot become nonpositive if a zero parameter is
excluded.  This is only the topological part of the deformation argument. -/
theorem positive_on_unitInterval_of_no_zero {m : ℝ → ℝ}
    (hm : ContinuousOn m (Icc 0 1)) (h0 : 0 < m 0)
    (hnz : ∀ t ∈ Icc (0 : ℝ) 1, m t ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, 0 < m t := by
  intro t ht
  by_contra htp
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' ht.1
    (hm.mono (Icc_subset_Icc le_rfl ht.2))
    (show (0 : ℝ) ∈ Icc (m t) (m 0) from ⟨le_of_not_gt htp, h0.le⟩)
  exact hnz s ⟨hs.1, hs.2.trans ht.2⟩ hsz

end PowerConvexity
