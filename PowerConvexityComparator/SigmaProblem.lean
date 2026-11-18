import PowerConvexityComparator.SupportProblem

/-! The actual sigma_super_harmonic inequality, with the nonnegative branch
explicitly assumed in the frozen section (line 488). -/
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexityComparator.SigmaProblem
open AppendixAProblem SeparationProblem SupportProblem

noncomputable def linearized (u f : CN 2 → ℝ) (x : CN 2) : ℝ :=
  (∑ i,∑ j,(mixed u x)⁻¹ j i*mixed f x i j).re

def SigmaStatement : Prop :=
  ∀ (U : Set (CN 2)), IsOpen U → ∀ (u : CN 2 → ℝ), ContDiffOn ℝ 4 u U →
    ∀ ρ : ℂ, ρ ≠ 0 → (∀ y ∈ U, (mixed u y).det = ρ) →
    (∀ y ∈ U, u y < 0) → (∀ y ∈ U, (mixed u y).PosDef) →
    (∀ y ∈ U, 0 ≤ sigma u y) → ∀ x ∈ U, 0 < discriminant (quotient u x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      linearized u (sigma u) y ≤ C*(sigma u y+‖fderiv ℝ (sigma u) y‖)

end PowerConvexityComparator.SigmaProblem
