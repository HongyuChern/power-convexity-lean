import PowerConvexity.Analysis.AsymptoticEquicontinuity

/-! # Actual minimizing points near a strict contact of a uniform limit.
Minimizers are constructed on the same compact set. Their convergence
uses separation from the unique strict minimum, without derivative data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Metric
open scoped Topology
namespace PowerConvexity

theorem compact_strict_minimizer_stability
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {x₀ : X} (hx₀ : x₀ ∈ K) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ n, ContinuousOn (f n) K) (hg : ContinuousOn g K)
    (hconv : TendstoUniformlyOn f g atTop K)
    (hstrict : ∀ x ∈ K, x ≠ x₀ → g x₀ < g x) :
    ∃ z : ℕ → X, (∀ n, z n ∈ K ∧ IsMinOn (f n) K (z n)) ∧
      Tendsto z atTop (𝓝 x₀) := by
  classical
  have hex (n : ℕ) : ∃ x ∈ K, IsMinOn (f n) K x :=
    hK.exists_isMinOn ⟨x₀,hx₀⟩ (hf n)
  choose z hz hm using hex
  refine ⟨z,fun n => ⟨hz n,hm n⟩,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let S : Set X := K \ ball x₀ ε
  have hS : IsCompact S := hK.diff isOpen_ball
  by_cases hSn : S.Nonempty
  · obtain ⟨y,hy,hmy⟩ := hS.exists_isMinOn hSn (hg.mono diff_subset)
    have hyne : y ≠ x₀ := by
      intro heq
      exact hy.2 (by simpa only [heq,mem_ball,dist_self] using hε)
    have hgap := hstrict y hy.1 hyne
    let δ : ℝ := (g y-g x₀)/3
    have hδ : 0 < δ := by dsimp only [δ]; linarith only [hgap]
    have hevent : ∀ᶠ n in atTop, ∀ x ∈ K, dist (g x) (f n x) < δ :=
      (Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ
    obtain ⟨N,hN⟩ := eventually_atTop.1 hevent
    refine ⟨N,?_⟩
    intro n hn
    by_contra hbad
    have hzn : z n ∈ S := ⟨hz n,by simpa only [mem_ball] using hbad⟩
    have hlow := hmy hzn
    have hmin := hm n hx₀
    have hb₀ := hN n hn x₀ hx₀
    have hbn := hN n hn (z n) (hz n)
    rw [Real.dist_eq,abs_lt] at hb₀ hbn
    dsimp only [δ] at hb₀ hbn
    change g y ≤ g (z n) at hlow
    change f n (z n) ≤ f n x₀ at hmin
    linarith only [hgap,hlow,hmin,hb₀.1,hbn.2]
  · refine ⟨0,fun n _ => ?_⟩
    have hx : z n ∉ S := fun h => hSn ⟨z n,h⟩
    have hb : z n ∈ ball x₀ ε := by
      by_contra h
      exact hx ⟨hz n,h⟩
    exact hb

end PowerConvexity
