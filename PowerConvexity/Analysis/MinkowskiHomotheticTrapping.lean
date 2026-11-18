import PowerConvexity.Analysis.ConvexThickening

/-! # Explicit homothetic trapping for the actual Minkowski domain path -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Metric
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def minkowskiDomain (t : ℝ) (A B : Set E) : Set E :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = t • a+(1-t) • b}

theorem minkowskiDomain_contains_inter (t : ℝ) (A B : Set E) : A ∩ B ⊆ minkowskiDomain t A B := by
  intro x hx
  refine ⟨x,hx.1,x,hx.2,?_⟩
  module

theorem minkowskiDomain_convex {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (t : ℝ) :
    Convex ℝ (minkowskiDomain t A B) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨xA,hxA,xB,hxB,rfl⟩ := hx
  obtain ⟨yA,hyA,yB,hyB,rfl⟩ := hy
  refine ⟨a • xA+b • yA,hA hxA hyA ha hb hab,
    a • xB+b • yB,hB hxB hyB ha hb hab,?_⟩
  module

theorem minkowskiDomain_nearby_point {A B : Set E} {L s t : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ ≤ L) (hB : ∀ b ∈ B, ‖b‖ ≤ L)
    {x : E} (hx : x ∈ minkowskiDomain t A B) :
    ∃ y ∈ minkowskiDomain s A B, ‖x-y‖ ≤ 2*L*|t-s| := by
  obtain ⟨a,ha,b,hb,rfl⟩ := hx
  refine ⟨s • a+(1-s) • b,⟨a,ha,b,hb,rfl⟩,?_⟩
  have he : t • a+(1-t) • b-(s • a+(1-s) • b) = (t-s) • (a-b) := by module
  rw [he,norm_smul,Real.norm_eq_abs]
  have hh : ‖a-b‖ ≤ 2*L := (norm_sub_le a b).trans (by linarith [hA a ha,hB b hb])
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (t-s))]

theorem minkowskiDomain_subset_dilation {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L) (s t : ℝ) :
    minkowskiDomain t A B ⊆ dilatedDomain (1+(2*L*|t-s|)/ρ) (minkowskiDomain s A B) := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := minkowskiDomain_nearby_point hAb hBb hx (s := s)
  have hball : closedBall (0:E) ρ ⊆ minkowskiDomain s A B :=
    fun z hz => minkowskiDomain_contains_inter s A B ⟨hballA hz,hballB hz⟩
  have hh := convex_add_small_vector_mem_dilation (minkowskiDomain_convex hA hB s)
    hρ (by positivity : 0 ≤ 2*L*|t-s|) hball hy hxy
  change (1+2*L*|t-s|/ρ)⁻¹ • x ∈ minkowskiDomain s A B
  simpa only [add_sub_cancel] using hh

theorem minkowskiDomain_homothetic_trapping {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L) (s t : ℝ) :
    let lam := 1+(2*L*|t-s|)/ρ
    dilatedDomain lam⁻¹ (minkowskiDomain s A B) ⊆ minkowskiDomain t A B ∧
      minkowskiDomain t A B ⊆ dilatedDomain lam (minkowskiDomain s A B) := by
  dsimp only
  refine ⟨?_,minkowskiDomain_subset_dilation hA hB hρ hL hballA hballB hAb hBb s t⟩
  intro x hx
  have hb := minkowskiDomain_subset_dilation hA hB hρ hL hballA hballB hAb hBb t s
  have hlam : 0 < 1+2*L*|t-s|/ρ := by positivity
  have he : 1+2*L*|s-t|/ρ = 1+2*L*|t-s|/ρ := by rw [abs_sub_comm s t]
  have hh := hb hx
  change (1+2*L*|s-t|/ρ)⁻¹ • ((1+2*L*|t-s|/ρ)⁻¹)⁻¹ • x ∈ minkowskiDomain t A B at hh
  rw [he,inv_inv,smul_smul,inv_mul_cancel₀ hlam.ne',one_smul] at hh
  exact hh

end PowerConvexity
