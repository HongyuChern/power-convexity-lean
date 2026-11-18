import PowerConvexityComparator.SeparationProblem
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.LocalExtr

/-! Independent statements for robustness, zero contact, and the corrected
perturbation-stability proposition. The boundary/start strictness in the last
statement is explicitly positive actual real Hessian. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexityComparator.SupportProblem
open AppendixAProblem SeparationProblem

noncomputable def power {n : ℕ} (u : CN n → ℝ) : CN n → ℝ := fun y => -Real.sqrt (-u y)

def PositiveHessian {n : ℕ} (f : CN n → ℝ) (x : CN n) : Prop :=
  ∀ v : CN n, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x v v

def RobustnessStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (CN n)), IsFiniteMeasureOnCompacts μ →
    ∀ (K : Set (CN n)), IsCompact K → ∀ (u : CN n → ℝ) (x : CN n),
    ContDiffAt ℝ 2 u x → u x < 0 → ∀ ε : ℝ, 0 < ε →
    (∀ q : CN n → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      u x+q x < 0 ∧ ∃ V : Set (CN n), IsOpen V ∧ x ∈ V ∧
        ConvexOn ℝ V (power (fun y => u y+q y))) →
    ∃ C : ℝ, 0 < C ∧ ∀ v : CN n, C*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ (power u)) x v v

noncomputable def discriminant (K : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  K.trace.re^2-4*K.det.re
noncomputable def sigma (u : CN 2 → ℝ) (x : CN 2) : ℝ :=
  ((quotient u x).trace.re-Real.sqrt (discriminant (quotient u x)))/2

def TouchStatement : Prop :=
  ∀ (U : Set (CN 2)), IsOpen U → ∀ (u : CN 2 → ℝ), ContDiffOn ℝ 4 u U →
    ∀ ρ : ℂ, ρ ≠ 0 → (∀ y ∈ U, (mixed u y).det = ρ) →
    (∀ y ∈ U, u y < 0) → (∀ y ∈ U, (mixed u y).PosDef) →
    ∀ x ∈ U, sigma u x = 0 → 0 < discriminant (quotient u x) →
      IsLocalMin (sigma u) x → ∀ᶠ y in 𝓝 x, sigma u y = 0

def StabilityStatement : Prop :=
  ∀ μ : Measure (CN 2), IsFiniteMeasureOnCompacts μ → Measure.IsOpenPosMeasure μ →
    ∀ K : Set (CN 2), IsCompact K → (interior K).Nonempty →
    ∀ U : Set (CN 2), IsOpen U → Convex ℝ U → IsPreconnected U →
    IsCompact (closure U) → U.Nonempty → ∀ u : CN 2 → ℝ,
    (∀ x ∈ closure U, ContDiffAt ℝ 4 u x) →
    ∀ ρ : ℂ, ρ ≠ 0 → (∀ y ∈ U, (mixed u y).det = ρ) →
    (∀ y ∈ closure U, (mixed u y).PosDef) → ∀ ε : ℝ, 0 < ε →
    (∀ q : CN 2 → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      ∀ y ∈ closure U, u y+q y < 0) →
    (∀ x ∈ closure U, PositiveHessian (power u) x) →
    (∀ q : CN 2 → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      ∀ x ∈ frontier U, PositiveHessian (power (fun y => u y+q y)) x) →
    (∀ q : CN 2 → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      StrictConvexOn ℝ U (power (fun y => u y+q y))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closure U, ∀ v : CN 2, v ≠ 0 →
      C*‖v‖^2 < fderiv ℝ (fderiv ℝ (power u)) x v v

end PowerConvexityComparator.SupportProblem
