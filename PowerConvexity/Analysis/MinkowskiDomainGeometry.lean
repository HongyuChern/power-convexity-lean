import PowerConvexity.Analysis.MinkowskiHomotheticTrapping
import PowerConvexity.Analysis.StrictBoundaryChords
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Endpoint geometry of the actual Minkowski path -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Pointwise Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem minkowskiDomain_eq_smul_add (t : ℝ) (A B : Set E) :
    minkowskiDomain t A B = t • A+(1-t) • B := by
  ext x
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨t • a,⟨a,ha,rfl⟩,(1-t) • b,⟨b,hb,rfl⟩,rfl⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨a,ha,b,hb,rfl⟩

theorem minkowskiDomain_zero {A B : Set E} (hA : A.Nonempty) : minkowskiDomain 0 A B = B := by
  ext x
  constructor
  · rintro ⟨a,ha,b,hb,hx⟩
    have he : x = b := by simpa only [zero_smul,sub_zero,one_smul,zero_add] using hx
    simpa only [he] using hb
  · intro hx
    obtain ⟨a,ha⟩ := hA
    exact ⟨a,ha,x,hx,by simp⟩

theorem minkowskiDomain_one {A B : Set E} (hB : B.Nonempty) : minkowskiDomain 1 A B = A := by
  ext x
  constructor
  · rintro ⟨a,ha,b,hb,hx⟩
    have he : x = a := by simpa only [one_smul,sub_self,zero_smul,add_zero] using hx
    simpa only [he] using ha
  · intro hx
    obtain ⟨b,hb⟩ := hB
    exact ⟨x,hx,b,hb,by simp⟩

theorem minkowskiDomain_isOpen {A B : Set E} (hA : IsOpen A) (hB : IsOpen B)
    (hAn : A.Nonempty) (t : ℝ) : IsOpen (minkowskiDomain t A B) := by
  by_cases ht : t = 0
  · rw [ht,minkowskiDomain_zero hAn]
    exact hB
  · rw [minkowskiDomain_eq_smul_add]
    exact (hA.smul₀ ht).add_right

theorem minkowskiDomain_norm_le {A B : Set E} {L t : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ ≤ L) (hB : ∀ b ∈ B, ‖b‖ ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : E} (hx : x ∈ minkowskiDomain t A B) : ‖x‖ ≤ L := by
  obtain ⟨a,ha,b,hb,rfl⟩ := hx
  have hh := norm_add_le (t • a) ((1-t) • b)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0,
    abs_of_nonneg (sub_nonneg.mpr ht1)] at hh
  have h1 := mul_le_mul_of_nonneg_left (hA a ha) ht0
  have h2 := mul_le_mul_of_nonneg_left (hB b hb) (sub_nonneg.mpr ht1)
  nlinarith

theorem minkowskiDomain_isCompact_closure [ProperSpace E] {A B : Set E} {L t : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ ≤ L) (hB : ∀ b ∈ B, ‖b‖ ≤ L)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsCompact (closure (minkowskiDomain t A B)) := by
  apply Bornology.IsBounded.isCompact_closure
  exact isBounded_iff_forall_norm_le.mpr ⟨L,fun _ hx => minkowskiDomain_norm_le hA hB ht0 ht1 hx⟩

theorem minkowskiDomain_closure {A B : Set E}
    (hA : IsCompact (closure A)) (hB : IsCompact (closure B)) (t : ℝ) :
    closure (minkowskiDomain t A B) = t • closure A+(1-t) • closure B := by
  rw [minkowskiDomain_eq_smul_add]
  apply subset_antisymm
  · apply (hA.smul t |>.add (hB.smul (1-t))).isClosed.closure_subset_iff.mpr
    exact add_subset_add (smul_set_mono subset_closure) (smul_set_mono subset_closure)
  · rw [← closure_smul₀,← closure_smul₀]
    rintro z ⟨x,hx,y,hy,rfl⟩
    exact map_mem_closure₂ continuous_add hx hy (fun a ha b hb => ⟨a,ha,b,hb,rfl⟩)

theorem minkowskiDomain_strictBoundaryChords [ProperSpace E]
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : HasStrictBoundaryChords A) (hB : HasStrictBoundaryChords B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hAK : IsCompact (closure A)) (hBK : IsCompact (closure B)) (t : ℝ) :
    HasStrictBoundaryChords (minkowskiDomain t A B) := by
  have hconv := minkowskiDomain_convex (strictBoundaryChords_convex hAo hA)
    (strictBoundaryChords_convex hBo hB) t
  have hne : (minkowskiDomain t A B).Nonempty := by
    obtain ⟨a,ha⟩ := hAn
    obtain ⟨b,hb⟩ := hBn
    exact ⟨t • a+(1-t) • b,⟨a,ha,b,hb,rfl⟩⟩
  apply (strictBoundaryChords_iff_strictConvex_closure
    (minkowskiDomain_isOpen hAo hBo hAn t) hconv hne).mpr
  rw [minkowskiDomain_closure hAK hBK]
  exact ((strictBoundaryChords_strictConvex_closure hAo hA).smul t).add
    ((strictBoundaryChords_strictConvex_closure hBo hB).smul (1-t))

end PowerConvexity
