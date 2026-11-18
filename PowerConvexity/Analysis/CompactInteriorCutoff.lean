import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # A nonnegative smooth interior cutoff dominating one on a compact set -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_C4_compact_interior_cutoff
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ chi : E → ℝ, ∃ N : Set E, IsCompact N ∧ N ⊆ U ∧ ContDiff ℝ 4 chi ∧
      (∀ x ∉ N, chi x = 0) ∧ (∀ x, 0 ≤ chi x) ∧ ∀ x ∈ K, 1 ≤ chi x := by
  classical
  have hb (p : K) := exists_contDiff_tsupport_subset (n := 4) (hU.mem_nhds (hKU p.property))
  choose b hbU hbK hbC hbI hb1 using hb
  let O : K → Set E := fun p => {x | (1 : ℝ)/2 < b p x}
  have hO (p : K) : IsOpen (O p) := isOpen_lt continuous_const (hbC p).continuous
  have hcover : K ⊆ ⋃ p : K, O p := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩,?_⟩
    change (1 : ℝ)/2 < b ⟨x,hx⟩ x
    rw [hb1]
    norm_num
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover O hO hcover
  let N : Set E := ⋃ p ∈ S, tsupport (b p)
  let chi : E → ℝ := fun x => 2*∑ p ∈ S, b p x
  have hb0 (p : K) (x : E) : 0 ≤ b p x := (hbI p (mem_range_self x)).1
  have hNK : IsCompact N := by
    exact S.finite_toSet.isCompact_biUnion (fun p _ => hbK p)
  have hNU : N ⊆ U := by
    intro x hx
    obtain ⟨p,hpS,hpx⟩ := mem_iUnion₂.mp hx
    exact hbU p hpx
  refine ⟨chi,N,hNK,hNU,contDiff_const.mul (ContDiff.sum (fun p _ => hbC p)),?_,?_,?_⟩
  · intro x hx
    have hz (p : K) (hp : p ∈ S) : b p x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hpx
      exact hx (mem_iUnion₂.mpr ⟨p,hp,hpx⟩)
    simp only [chi,Finset.sum_eq_zero hz,mul_zero]
  · intro x
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ => hb0 p x))
  · intro x hx
    obtain ⟨p,hpS,hpx⟩ := mem_iUnion₂.mp (hS hx)
    have hp : (1 : ℝ)/2 < b p x := hpx
    have hle := Finset.single_le_sum (fun q _ => hb0 q x) hpS
    dsimp only [chi]
    linarith

end PowerConvexity
