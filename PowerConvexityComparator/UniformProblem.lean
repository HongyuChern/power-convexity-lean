import PowerConvexityComparator.SupportProblem

/-! The quantitative content of robustness: C is chosen before the potential
and the center. All Hessians and perturbations are spelled out independently.
-/
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff
namespace PowerConvexityComparator.UniformProblem
open AppendixAProblem SeparationProblem SupportProblem

def UniformRobustnessStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (CN n)), IsFiniteMeasureOnCompacts μ →
    ∀ (K X : Set (CN n)), IsCompact K → Bornology.IsBounded X →
    ∀ (ε m : ℝ), 0 < ε → m < 0 →
    ∃ C : ℝ, 0 < C ∧ ∀ (u : CN n → ℝ) (x : CN n), x ∈ X →
      ContDiffAt ℝ 2 u x → m ≤ u x → u x < 0 →
      (∀ q : CN n → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
        ∀ v : CN n, 0 ≤ fderiv ℝ (fderiv ℝ (power (fun y => u y+q y))) x v v) →
      ∀ v : CN n, C*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ (power u)) x v v

end PowerConvexityComparator.UniformProblem
