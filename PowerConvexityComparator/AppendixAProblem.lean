import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Independent frozen statements of Appendix A. This file imports only
Mathlib; every Hessian below is an actual real Frechet derivative. The sole
correction to A1 is the necessary nonzero mixed-Hessian determinant. -/
set_option autoImplicit false
open scoped ContDiff Matrix
namespace PowerConvexityComparator.AppendixAProblem

abbrev CN (n : ℕ) := EuclideanSpace ℂ (Fin n)
noncomputable def xAxis {n : ℕ} (i : Fin n) : CN n := EuclideanSpace.single i 1
noncomputable def yAxis {n : ℕ} (i : Fin n) : CN n := Complex.I • xAxis i

noncomputable def mixed {n : ℕ} (u : CN n → ℝ) (x : CN n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (4 : ℂ)⁻¹ *
    ((fderiv ℝ (fderiv ℝ u) x (xAxis i) (xAxis j) : ℂ) +
      (fderiv ℝ (fderiv ℝ u) x (yAxis i) (yAxis j) : ℂ) +
      Complex.I * ((fderiv ℝ (fderiv ℝ u) x (xAxis i) (yAxis j) : ℂ) -
        (fderiv ℝ (fderiv ℝ u) x (yAxis i) (xAxis j) : ℂ)))

noncomputable def pure {n : ℕ} (u : CN n → ℝ) (x : CN n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (4 : ℂ)⁻¹ *
    ((fderiv ℝ (fderiv ℝ u) x (xAxis i) (xAxis j) : ℂ) -
      (fderiv ℝ (fderiv ℝ u) x (yAxis i) (yAxis j) : ℂ) -
      Complex.I * ((fderiv ℝ (fderiv ℝ u) x (xAxis i) (yAxis j) : ℂ) +
        (fderiv ℝ (fderiv ℝ u) x (yAxis i) (xAxis j) : ℂ)))

noncomputable def realMatrix {n : ℕ} (u : CN n → ℝ) (x : CN n) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ u) x
    (if i.2 = 0 then xAxis i.1 else yAxis i.1)
    (if j.2 = 0 then xAxis j.1 else yAxis j.1)

def A1Statement : Prop :=
  ∀ (n : ℕ) (u : CN n → ℝ) (x : CN n), ContDiffAt ℝ 2 u x → (mixed u x).det ≠ 0 →
    (1 - pure u x * ((mixed u x).map star)⁻¹ * (pure u x).map star * (mixed u x)⁻¹).det =
      ((realMatrix u x).det : ℂ) / ((4 : ℂ)^n * (mixed u x).det^2)

def A2Statement : Prop :=
  ∀ (A B C β γ : ℝ), 0 < B → 0 < C →
    ((Matrix.of ![![A,β,γ],![β,B,0],![γ,0,C]]).PosSemidef ↔ 0 ≤ A-β^2/B-γ^2/C)

end PowerConvexityComparator.AppendixAProblem
