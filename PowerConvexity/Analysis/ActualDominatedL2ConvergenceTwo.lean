import PowerConvexity.Analysis.ActualZeroTraceLimitTwo

/-! # Strong L2 convergence under an actual L2 majorant -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace PowerConvexity
open DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_dominated_L2_convergence_two {μ : Measure E}
    {F : ℕ → E → ℝ} {g b : E → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hg : MemLp g 2 μ)
    (hb : MemLp b 2 μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (fun x => F n x-g x) 2 μ) atTop (𝓝 0) := by
  have hmono (n : ℕ) (s : Set E) :
      eLpNorm (s.indicator (F n)) 2 μ ≤ eLpNorm (s.indicator b) 2 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hbound n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs,le_refl]
  have hui : UnifIntegrable F 2 μ := by
    have hh : UnifIntegrable (fun _ : ℕ => b) 2 μ :=
      unifIntegrable_const (by norm_num) (by simp) hb
    intro ε hε
    obtain ⟨δ,hδ,hδb⟩ := hh hε
    exact ⟨δ,hδ,fun n s hs hμs => (hmono n s).trans (hδb n s hs hμs)⟩
  have hut : UnifTight F 2 μ := by
    have hh : UnifTight (fun _ : ℕ => b) 2 μ := unifTight_const (by simp) hb
    intro ε hε
    obtain ⟨s,hs,hbs⟩ := hh hε
    exact ⟨s,hs,fun n => (hmono n sᶜ).trans (hbs n)⟩
  exact tendsto_Lp_of_tendsto_ae (by norm_num) (by simp) hF hg hui hut hlim

end PowerConvexity
