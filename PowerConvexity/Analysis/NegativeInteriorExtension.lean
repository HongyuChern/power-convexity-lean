import PowerConvexity.Analysis.CompactInteriorCutoff

/-! # Make an ambient C4 boundary function negative inside without changing its boundary germs -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_C4_negative_extension_preserving_boundary_germs
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {rho : E → ℝ} (hrho : ContDiff ℝ 4 rho)
    {W : Set E} (hWo : IsOpen W) (hKW : frontier U ⊆ W)
    (hneg : ∀ x ∈ U ∩ W, rho x < 0) :
    ∃ f : E → ℝ, ContDiff ℝ 4 f ∧ (∀ x ∈ U, f x < 0) ∧
      ∃ V : Set E, IsOpen V ∧ frontier U ⊆ V ∧ EqOn f rho V := by
  have hKU : closure U \ W ⊆ U := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hx.1,hn⟩
    exact hx.2 (hKW hxf)
  obtain ⟨chi,N,hNK,hNU,hchi,hchi0,hchin,hchi1⟩ :=
    exists_C4_compact_interior_cutoff (hK.diff hWo) hU hKU
  obtain ⟨L,hL⟩ := (hK.image hrho.continuous).isBounded.exists_norm_le
  let M := max L 0+1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_right L 0]
  have hrbound (x : E) (hx : x ∈ U) : rho x < M := by
    have hh := hL (rho x) (mem_image_of_mem rho (subset_closure hx))
    have hh' : rho x ≤ L := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)
    dsimp only [M]
    linarith [le_max_left L 0]
  let f : E → ℝ := fun x => rho x-M*chi x
  refine ⟨f,hrho.sub (contDiff_const.mul hchi),?_,Nᶜ,hNK.isClosed.isOpen_compl,?_,?_⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · have hn := hneg x ⟨hx,hxW⟩
      have hm := mul_nonneg hM.le (hchin x)
      dsimp only [f]
      linarith
    · have h1 := hchi1 x ⟨subset_closure hx,hxW⟩
      have hm := mul_le_mul_of_nonneg_left h1 hM.le
      have hb := hrbound x hx
      dsimp only [f]
      nlinarith
  · intro x hx hxN
    have hxnot : x ∉ U := by rw [hU.frontier_eq] at hx; exact hx.2
    exact hxnot (hNU hxN)
  · intro x hx
    dsimp only [f]
    rw [hchi0 x hx,mul_zero,sub_zero]

end PowerConvexity
