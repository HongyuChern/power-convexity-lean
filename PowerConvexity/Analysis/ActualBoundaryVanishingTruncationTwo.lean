import PowerConvexity.Analysis.ActualZeroTraceLimitTwo
import PowerConvexity.Calculus.ClosureJetSobolev

/-! # Smooth scalar truncations which vanish on a genuine boundary collar

The cutoff is applied to the value of a positive boundary-vanishing function.
Its derivative bound is independent of the cutoff scale. No trace theorem is
assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def actualBoundaryValueCutoffTwo (n : ℕ) (t : ℝ) : ℝ :=
  t * Real.smoothTransition (((n : ℝ)+1)*t-1)

theorem actual_boundary_value_cutoff_contDiff_two (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (actualBoundaryValueCutoffTwo n) := by
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem actual_boundary_value_cutoff_zero_two (n : ℕ) {t : ℝ}
    (ht : ((n : ℝ)+1)*t ≤ 1) : actualBoundaryValueCutoffTwo n t = 0 := by
  rw [actualBoundaryValueCutoffTwo, Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem actual_boundary_value_cutoff_abs_le_two (n : ℕ) (t : ℝ) :
    |actualBoundaryValueCutoffTwo n t| ≤ |t| := by
  rw [actualBoundaryValueCutoffTwo, abs_mul,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)

theorem actual_smooth_transition_deriv_bound_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).continuous_deriv_one
  obtain ⟨m, -, hm⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) hcont.norm.continuousOn
  refine ⟨|deriv Real.smoothTransition m|, abs_nonneg _, fun t => ?_⟩
  by_cases ht0 : t < 0
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht0] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [he.deriv_eq, deriv_const, abs_zero]
    exact abs_nonneg _
  · by_cases ht1 : 1 < t
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds ht1] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact abs_nonneg _
    · exact Filter.eventually_principal.mp hm t ⟨le_of_not_gt ht0,le_of_not_gt ht1⟩

theorem actual_boundary_value_cutoff_deriv_two (n : ℕ) (t : ℝ) :
    deriv (actualBoundaryValueCutoffTwo n) t =
      Real.smoothTransition (((n : ℝ)+1)*t-1) +
        (((n : ℝ)+1)*t)*deriv Real.smoothTransition (((n : ℝ)+1)*t-1) := by
  have hst := (Real.smoothTransition.contDiff.differentiable one_ne_zero
    (((n : ℝ)+1)*t-1)).hasDerivAt
  have hl : HasDerivAt (fun s : ℝ => ((n : ℝ)+1)*s-1) ((n : ℝ)+1) t := by
    simpa using ((hasDerivAt_id t).const_mul ((n : ℝ)+1)).sub_const 1
  have hh := (hasDerivAt_id t).mul (hst.comp t hl)
  have hh' := hh.deriv
  simp only [Pi.mul_apply,Function.comp_def,id_eq,one_mul] at hh'
  change deriv (fun s : ℝ => s*Real.smoothTransition (((n : ℝ)+1)*s-1)) t = _
  have he : (fun s : ℝ => s*Real.smoothTransition (((n : ℝ)+1)*s-1)) =
      id * (fun s : ℝ => Real.smoothTransition (((n : ℝ)+1)*s-1)) := by
    funext s
    rfl
  rw [he,hh']
  ring

theorem actual_boundary_value_cutoff_deriv_bound_two :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n t, |deriv (actualBoundaryValueCutoffTwo n) t| ≤ D := by
  obtain ⟨C,hC,hbound⟩ := actual_smooth_transition_deriv_bound_two
  refine ⟨1+2*C, by positivity, fun n t => ?_⟩
  let s : ℝ := ((n : ℝ)+1)*t-1
  have ht : ((n : ℝ)+1)*t = s+1 := by dsimp [s]; ring
  rw [actual_boundary_value_cutoff_deriv_two]
  change |Real.smoothTransition s + (((n : ℝ)+1)*t)*deriv Real.smoothTransition s| ≤ _
  rw [ht]
  have hfirst : |Real.smoothTransition s| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hsecond : |(s+1)*deriv Real.smoothTransition s| ≤ 2*C := by
    by_cases hs0 : s < 0
    · have he : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hs0] with r hr
        exact Real.smoothTransition.zero_of_nonpos hr.le
      rw [he.deriv_eq,deriv_const,mul_zero,abs_zero]
      positivity
    · by_cases hs1 : 1 < s
      · have he : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds hs1] with r hr
          exact Real.smoothTransition.one_of_one_le hr.le
        rw [he.deriv_eq,deriv_const,mul_zero,abs_zero]
        positivity
      · have hs : 0 ≤ s ∧ s ≤ 1 := ⟨le_of_not_gt hs0,le_of_not_gt hs1⟩
        rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ s+1)]
        exact mul_le_mul (by linarith) (hbound s) (abs_nonneg _) (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem actual_boundary_value_cutoff_eventually_identity_two {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, actualBoundaryValueCutoffTwo n =ᶠ[𝓝 t] id := by
  have hn : ∀ᶠ n : ℕ in atTop, (⌈3/t⌉₊ : ℕ) ≤ n := eventually_ge_atTop _
  filter_upwards [hn] with n hn
  have hnt : 3/t ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hgt : 2 < ((n : ℝ)+1)*t := by
    have hh := (div_le_iff₀ ht).mp hnt
    nlinarith
  have hnhds : {s : ℝ | 2 < ((n : ℝ)+1)*s} ∈ 𝓝 t :=
    (isOpen_lt continuous_const (continuous_const.mul continuous_id)).mem_nhds hgt
  filter_upwards [hnhds] with s hs
  simp only [actualBoundaryValueCutoffTwo,id_eq,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ ((n : ℝ)+1)*s-1),mul_one]

end PowerConvexity
