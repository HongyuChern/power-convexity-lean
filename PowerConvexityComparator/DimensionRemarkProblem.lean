import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-! Independent algebraic statements of frozen equations 11.1--11.2 and the
preceding higher-dimensional counterexample. These concern matrices, not PDE
solutions or realizability of prescribed third-order jets.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace PowerConvexityComparator.DimensionRemarkProblem

def ScalarIdentityStatement : Prop :=
  ∀ m C : ℝ,
    m+m^2/(C^2+1)^2-(m*(1-1/(C^2+1)))^2 = m-m^2+2*m^2/(C^2+1)

def CounterexampleStatement : Prop :=
  ∀ n : ℕ, 2 < n → ∃ (W : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℂ),
    W.conjTranspose = -W ∧
    (∑ p,∑ q,((1 : Matrix (Fin n) (Fin n) ℂ) q p+r q*star (r p))*W p q) = 0 ∧
    (∑ p,∑ q,Complex.normSq (W p q)) < Complex.normSq W.trace

end PowerConvexityComparator.DimensionRemarkProblem
