import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Independent statement of frozen Appendix B, corrected only by a local
real-spectrum hypothesis. Actual Frechet derivatives are written out and no
project jet, differential operator or spectral function is imported. -/
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
namespace PowerConvexityComparator.AppendixBProblem
abbrev CN (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable def maximumEigenvalue {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {t : ℝ | Module.End.HasEigenvalue K.toLin' (t:ℂ)}
noncomputable def minimumEigenvalue {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t : ℝ | Module.End.HasEigenvalue K.toLin' (t:ℂ)}

def Conclusion {n : ℕ} (K : CN n → Matrix (Fin n) (Fin n) ℂ)
    (f : CN n → ℝ) (x : CN n) (i : Fin n) (d : Fin n → ℝ) : Prop :=
  ContDiffAt ℝ 2 f x ∧ f x = d i ∧ ∀ a c : CN n,
    fderiv ℝ (fun y => (f y:ℂ)) x a = fderiv ℝ (fun y => K y i i) x a ∧
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z:ℂ)) y a) x c =
      fderiv ℝ (fun y => fderiv ℝ (fun z => K z i i) y a) x c +
      ∑ j : {j : Fin n // j ≠ i},
        (fderiv ℝ (fun y => K y i j) x a * fderiv ℝ (fun y => K y j i) x c +
          fderiv ℝ (fun y => K y i j) x c * fderiv ℝ (fun y => K y j i) x a) /
          ((d i:ℂ)-(d j:ℂ))

def MaximumStatement : Prop :=
  ∀ (n : ℕ) (K : CN n → Matrix (Fin n) (Fin n) ℂ) (x : CN n),
    (∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x) →
    ∀ (i : Fin n) (d : Fin n → ℝ), K x = Matrix.diagonal (fun j => (d j:ℂ)) →
    (∀ j, j ≠ i → d j < d i) →
    (∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) →
    Conclusion K (fun y => maximumEigenvalue (K y)) x i d

def MinimumStatement : Prop :=
  ∀ (n : ℕ) (K : CN n → Matrix (Fin n) (Fin n) ℂ) (x : CN n),
    (∀ j k, ContDiffAt ℝ 2 (fun y => K y j k) x) →
    ∀ (i : Fin n) (d : Fin n → ℝ), K x = Matrix.diagonal (fun j => (d j:ℂ)) →
    (∀ j, j ≠ i → d i < d j) →
    (∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0) →
    Conclusion K (fun y => minimumEigenvalue (K y)) x i d

end PowerConvexityComparator.AppendixBProblem
