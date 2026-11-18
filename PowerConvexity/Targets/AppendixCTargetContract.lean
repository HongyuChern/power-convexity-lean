import PowerConvexity.Calculus.AppendixCMain

/-! # Separately stated dimension-one target contracts

These are checked Lean statements with the geometric predicate expanded and
with an explicit strict chord conclusion. This is a partial target contract,
not an independent complete-paper Comparator or a Codex acceptance receipt.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem appendixC_target_strict_chord
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hstrict : StrictConvex ℝ U)
    (hsmooth : ∀ x ∈ frontier U, ∃ f : ℂ → ℝ, ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧
      fderiv ℝ f x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
    {u : ℂ → ℝ} (hu4 : ContDiffOn ℝ 4 u U) (hJ : Nonempty (ClosureC2Jet u U))
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (hdet : ∀ x ∈ U, (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).det = 1) :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ∀ a b : ℝ, 0 < a → 0 < b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) < a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) := by
  have hh := appendixC_main_strictConvexOn hU hbounded hstrict hsmooth
    (show C2OnClosure u U from ⟨hu4.of_le (by norm_num),hJ⟩) hboundary hdet
  intro x hx y hy hxy a b ha hb hab
  exact hh.2 hx hy hxy ha hb hab

theorem appendixC_target_positive_realHessian
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hstrict : StrictConvex ℝ U) (hsmooth : HasSmoothLocalDefiningFunction U)
    {u : ℂ → ℝ} (hu : C2OnClosure u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (hdet : ∀ x ∈ U, (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).det = 1) :
    ∀ x ∈ U, ∀ v : ℂ, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun y => -Real.sqrt (-u y))) x v v := by
  apply scalarDirichlet_positive_Hessian_of_C2_boundary hU hstrict.convex hbounded.isCompact_closure
    (smoothLocalDefiningFunction_implies_C2 hsmooth) hu.jet.continuous_value hu.1 hboundary
    (ρ := 1) (by norm_num)
  intro x hx
  simpa only [Matrix.det_fin_one,Complex.ofReal_one] using hdet x hx

end PowerConvexity
