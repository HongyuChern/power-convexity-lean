import PowerConvexity.Calculus.MinkowskiFamilyC0Two
import PowerConvexity.Analysis.CompactSmallParameter

/-! # Interior stability of the physical Minkowski domains -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem minkowskiDomain_joint_mem_nhds
    {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
    {s : Icc (0:ℝ) 1} (hV : IsOpen (minkowskiDomain s A B))
    {x : E} (hx : x ∈ minkowskiDomain s A B) :
    ∀ᶠ p : Icc (0:ℝ) 1 × E in 𝓝 (s,x), p.2 ∈ minkowskiDomain p.1 A B := by
  let lam : Icc (0:ℝ) 1 × E → ℝ := fun p => 1+2*L*|(p.1:ℝ)-(s:ℝ)|/ρ
  have hc : Continuous lam := by fun_prop
  have hl : Tendsto lam (𝓝 (s,x)) (𝓝 1) := by
    simpa only [lam,sub_self,abs_zero,mul_zero,zero_div,add_zero] using
      (hc.continuousAt (x := (s,x))).tendsto
  have hi : Tendsto (fun p => (lam p)⁻¹) (𝓝 (s,x)) (𝓝 1) := by
    simpa only [inv_one] using hl.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  apply eventually_mem_of_homothetic_inner_trapping hV hi continuousAt_snd.tendsto hx
  exact Filter.Eventually.of_forall fun p =>
    (minkowskiDomain_homothetic_trapping hA hB hρ hL hballA hballB hAb hBb (s:ℝ) (p.1:ℝ)).1

theorem minkowskiDomain_compact_eventually_subset
    {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
    {s : Icc (0:ℝ) 1} (hV : IsOpen (minkowskiDomain s A B))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ minkowskiDomain s A B) :
    ∀ᶠ t : Icc (0:ℝ) 1 in 𝓝 s, K ⊆ minkowskiDomain t A B := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  exact minkowskiDomain_joint_mem_nhds hA hB hρ hL hballA hballB hAb hBb hV (hKU hx)

theorem minkowskiDomain_eventually_contains_closedBall [ProperSpace E]
    {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
    {s : Icc (0:ℝ) 1} (hV : IsOpen (minkowskiDomain s A B))
    {x : E} (hx : x ∈ minkowskiDomain s A B) :
    ∃ R > 0, closedBall x R ⊆ minkowskiDomain s A B ∧
      ∀ᶠ t : Icc (0:ℝ) 1 in 𝓝 s, closedBall x R ⊆ minkowskiDomain t A B := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx)
  have hR : 0 < r/2 := by positivity
  have hb : closedBall x (r/2) ⊆ minkowskiDomain s A B :=
    (closedBall_subset_ball (by linarith : r/2 < r)).trans hsub
  exact ⟨r/2,hR,hb,minkowskiDomain_compact_eventually_subset hA hB hρ hL
    hballA hballB hAb hBb hV (isCompact_closedBall x (r/2)) hb⟩

end PowerConvexity
