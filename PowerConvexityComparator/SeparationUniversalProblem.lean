import PowerConvexityComparator.SeparationProblem

/-! The universal quantifier in frozen lemma:Seperation: every minimizer,
not only one selected attaining polynomial, has a simple least root. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexityComparator.SeparationUniversalProblem
open AppendixAProblem SeparationProblem

def UniversalSeparationStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ μ : Measure (CN n),
    IsFiniteMeasureOnCompacts μ → Measure.IsOpenPosMeasure μ →
    ∀ K : Set (CN n), IsCompact K → (interior K).Nonempty →
    ∀ (u : CN n → ℝ) (x : CN n), ContDiffAt ℝ 2 u x →
    ∀ ε : ℝ, 0 < ε →
    (∀ r : CN n → ℝ, PluriharmonicQuadratic r → energy μ K r ≤ ε → u x+r x < 0) →
    (∀ r : CN n → ℝ, PluriharmonicQuadratic r → energy μ K r ≤ ε →
      (mixed (fun y => -Real.sqrt (-(u y+r y))) x).PosDef) →
    ∀ q : CN n → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      (∀ r : CN n → ℝ, PluriharmonicQuadratic r → energy μ K r ≤ ε →
        minimumRoot (quotient (fun y => u y+q y) x) ≤
          minimumRoot (quotient (fun y => u y+r y) x)) →
      SimpleLeastSpectrum (quotient (fun y => u y+q y) x)

end PowerConvexityComparator.SeparationUniversalProblem
