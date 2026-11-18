import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.Order.DenselyOrdered

/-! # A geometric strict-domain predicate with boundary endpoints

For an open set Mathlib.StrictConvex is equivalent to convexity. The predicate
below explicitly quantifies over distinct endpoints in the closure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasStrictBoundaryChords (U : Set E) : Prop :=
  ∀ x ∈ closure U, ∀ y ∈ closure U, x ≠ y →
    ∀ a b : ℝ, 0 < a → 0 < b → a+b = 1 → a • x+b • y ∈ U

theorem open_mathlib_strictConvex_iff_convex {U : Set E} (hU : IsOpen U) :
    StrictConvex ℝ U ↔ Convex ℝ U := hU.strictConvex_iff

theorem strictBoundaryChords_mathlib_strictConvex {U : Set E}
    (hU : IsOpen U) (h : HasStrictBoundaryChords U) : StrictConvex ℝ U := by
  intro x hx y hy hxy a b ha hb hab
  rw [hU.interior_eq]
  exact h x (subset_closure hx) y (subset_closure hy) hxy a b ha hb hab

theorem strictBoundaryChords_convex {U : Set E}
    (hU : IsOpen U) (h : HasStrictBoundaryChords U) : Convex ℝ U :=
  (strictBoundaryChords_mathlib_strictConvex hU h).convex

theorem strictBoundaryChords_strictConvex_closure {U : Set E}
    (hU : IsOpen U) (h : HasStrictBoundaryChords U) : StrictConvex ℝ (closure U) := by
  intro x hx y hy hxy a b ha hb hab
  have hsub : U ⊆ interior (closure U) := hU.subset_interior_iff.mpr subset_closure
  exact hsub (h x hx y hy hxy a b ha hb hab)

theorem strictBoundaryChords_iff_strictConvex_closure {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty) :
    HasStrictBoundaryChords U ↔ StrictConvex ℝ (closure U) := by
  refine ⟨strictBoundaryChords_strictConvex_closure hU,?_⟩
  intro h x hx y hy hxy a b ha hb hab
  have hi : (interior U).Nonempty := hU.interior_eq.symm ▸ hne
  have he := hconv.interior_closure_eq_interior_of_nonempty_interior hi
  rw [hU.interior_eq] at he
  exact he ▸ h hx hy hxy ha hb hab

def openSquare : Set (ℝ × ℝ) := Ioo (-1) 1 ×ˢ Ioo (-1) 1

theorem openSquare_isOpen : IsOpen openSquare := isOpen_Ioo.prod isOpen_Ioo

theorem openSquare_mathlib_strictConvex : StrictConvex ℝ openSquare :=
  Convex.strictConvex_of_isOpen openSquare_isOpen
    ((convex_Ioo (-1:ℝ) 1).prod (convex_Ioo (-1:ℝ) 1))

theorem openSquare_not_strictBoundaryChords : ¬HasStrictBoundaryChords openSquare := by
  intro h
  have hc : closure openSquare = Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1 := by
    rw [openSquare,closure_prod_eq,closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
  have hx : ((-1,1) : ℝ × ℝ) ∈ closure openSquare := by rw [hc]; norm_num
  have hy : ((1,1) : ℝ × ℝ) ∈ closure openSquare := by rw [hc]; norm_num
  have hh := h (-1,1) hx (1,1) hy (by norm_num)
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [openSquare] at hh

end PowerConvexity
