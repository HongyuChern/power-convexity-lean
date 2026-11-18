import PowerConvexity.Analysis.CompactSmallParameter

/-! # One positive scaling for a continuous positive function on a compact set -/
set_option autoImplicit false
open Set
namespace PowerConvexity
variable {X : Type*} [TopologicalSpace X]

theorem exists_uniform_square_scaling_gt_one
    {K : Set X} (hK : IsCompact K) {d : X → ℝ} (hd : Continuous d)
    (hpos : ∀ x ∈ K, 0 < d x) :
    ∃ c > 1, ∀ x ∈ K, 1 < c^2*d x := by
  let O : ℝ → Set X := fun a => {x | 0 < d x ∧ 1 < a*d x}
  have hopen (a : ℝ) : IsOpen (O a) :=
    (isOpen_lt continuous_const hd).inter
      (isOpen_lt continuous_const (continuous_const.mul hd))
  have hcover : K ⊆ ⋃ a : ℝ, O a := by
    intro x hx
    refine mem_iUnion.mpr ⟨1/d x+1,hpos x hx,?_⟩
    change 1 < (1/d x+1)*d x
    rw [add_mul,one_mul,div_mul_cancel₀ _ (hpos x hx).ne']
    linarith [hpos x hx]
  have hdir : Directed (· ⊆ ·) O := by
    intro a b
    refine ⟨max a b,?_,?_⟩
    · intro x hx
      exact ⟨hx.1,hx.2.trans_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.1.le)⟩
    · intro x hx
      exact ⟨hx.1,hx.2.trans_le (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.1.le)⟩
  obtain ⟨a,ha⟩ := hK.elim_directed_cover O hopen hcover hdir
  let c := max a 1+1
  have hc : 1 < c := by dsimp only [c]; linarith [le_max_right a 1]
  have hac : a ≤ c^2 := by
    have h1 := le_max_left a 1
    have h2 := le_max_right a 1
    dsimp only [c]
    nlinarith [sq_nonneg (max a 1)]
  refine ⟨c,hc,?_⟩
  intro x hx
  exact (ha hx).2.trans_le (mul_le_mul_of_nonneg_right hac (hpos x hx).le)

end PowerConvexity
