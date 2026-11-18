import PowerConvexity.Analysis.ParameterMinimum

/-! # First contact using only positive-parameter continuity

Continuity at zero is not assumed. An actual positive initial segment, or an
actual positive anchor when zeros have already been excluded, is still needed.
-/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
local notation "I" => Icc (0 : ℝ) 1

theorem unitInterval_positive_of_positive_anchor_no_zero
    {m : I → ℝ} (hm : ∀ s : I, 0 < (s : ℝ) → ContinuousAt m s)
    (hnz : ∀ s : I, 0 < (s : ℝ) → m s ≠ 0)
    {s₀ : I} (hs₀ : 0 < (s₀ : ℝ)) (h₀ : 0 < m s₀) :
    ∀ s : I, 0 < (s : ℝ) → 0 < m s := by
  let P := Ioc (0 : ℝ) 1
  letI : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  let lift : P → I := fun s => ⟨s.1,s.2.1.le,s.2.2⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hmc : Continuous (fun s : P => m (lift s)) :=
    continuous_iff_continuousAt.mpr (fun s => (hm (lift s) s.2.1).comp hlift.continuousAt)
  intro s hs
  let p : P := ⟨s.1,hs,s.2.2⟩
  let p₀ : P := ⟨s₀.1,hs₀,s₀.2.2⟩
  by_contra hh
  obtain ⟨q,_,hq⟩ := isPreconnected_univ.intermediate_value
    (mem_univ p) (mem_univ p₀) hmc.continuousOn
    (show (0 : ℝ) ∈ Icc (m (lift p)) (m (lift p₀)) from ⟨le_of_not_gt hh,h₀.le⟩)
  exact hnz (lift q) q.2.1 hq

theorem unitInterval_positive_initial_segment_of_eventually_positive
    {m : I → ℝ} (h : ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I), 0 < m t) :
    ∃ a : I, 0 < (a : ℝ) ∧ ∀ t : I, t ≤ a → 0 < m t := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp h
  let α : ℝ := min (r/2) (1/2)
  have hα : 0 < α := lt_min (half_pos hr) (by norm_num)
  have hα1 : α ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hαr : α < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  let a : I := ⟨α,hα.le,hα1⟩
  refine ⟨a,hα,?_⟩
  intro t ht
  apply hball
  rw [mem_ball,Subtype.dist_eq,Real.dist_eq,sub_zero,abs_of_nonneg t.2.1]
  exact (show (t : ℝ) ≤ α from ht).trans_lt hαr

theorem unitInterval_exists_first_zero_of_positive_initial_segment
    {m : I → ℝ} (hm : ∀ s : I, 0 < (s : ℝ) → ContinuousAt m s)
    {a : I} (ha : 0 < (a : ℝ))
    (hinit : ∀ t : I, t ≤ a → 0 < m t)
    (h1 : m ⟨1,by norm_num⟩ ≤ 0) :
    ∃ s : I, 0 < (s : ℝ) ∧ m s = 0 ∧
      ∀ t : I, (t : ℝ) < (s : ℝ) → 0 < m t := by
  let one : I := ⟨1,by norm_num⟩
  have ha1 : a ≤ one := a.2.2
  have hmc : ContinuousOn m (Icc a one) := by
    intro t ht
    exact (hm t (ha.trans_le ht.1)).continuousWithinAt
  obtain ⟨s,hs,hsz⟩ := intermediate_value_Icc' ha1 hmc
    (show (0 : ℝ) ∈ Icc (m one) (m a) from ⟨h1,(hinit a le_rfl).le⟩)
  let Z : Set I := Icc a one ∩ m ⁻¹' ({0} : Set ℝ)
  have hZclosed : IsClosed Z :=
    hmc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZ : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed (fun _ hz => hz.1)
  obtain ⟨s₀,hs₀,hmin⟩ := hZ.exists_isMinOn (show Z.Nonempty from ⟨s,hs,hsz⟩)
    continuous_subtype_val.continuousOn
  refine ⟨s₀,ha.trans_le hs₀.1.1,hs₀.2,?_⟩
  intro t ht
  by_cases hta : t ≤ a
  · exact hinit t hta
  have hat : a ≤ t := (lt_of_not_ge hta).le
  have ht1 : t ≤ one := t.2.2
  by_contra htp
  obtain ⟨r,hr,hrz⟩ := intermediate_value_Icc' hat
    (hmc.mono (Icc_subset_Icc le_rfl ht1))
    (show (0 : ℝ) ∈ Icc (m t) (m a) from ⟨le_of_not_gt htp,(hinit a le_rfl).le⟩)
  have hrZ : r ∈ Z := ⟨⟨hr.1,hr.2.trans ht1⟩,hrz⟩
  have hsr : (s₀ : ℝ) ≤ (r : ℝ) := hmin hrZ
  have hrt : (r : ℝ) ≤ (t : ℝ) := hr.2
  linarith

theorem unitInterval_exists_first_zero_of_eventually_positive
    {m : I → ℝ} (hm : ∀ s : I, 0 < (s : ℝ) → ContinuousAt m s)
    (hinit : ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I), 0 < m t)
    (h1 : m ⟨1,by norm_num⟩ ≤ 0) :
    ∃ s : I, 0 < (s : ℝ) ∧ m s = 0 ∧
      ∀ t : I, (t : ℝ) < (s : ℝ) → 0 < m t := by
  obtain ⟨a,ha,hpos⟩ := unitInterval_positive_initial_segment_of_eventually_positive hinit
  exact unitInterval_exists_first_zero_of_positive_initial_segment hm ha hpos h1

end PowerConvexity
