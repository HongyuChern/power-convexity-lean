import PowerConvexityComparator.AppendixAProblem
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Independent general-dimensional Appendix A separation problem. Only
Mathlib and the previously frozen Mathlib-only coordinate definitions occur.
All derivative, polynomial, L2, minimum-root and multiplicity data are explicit. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexityComparator.SeparationProblem
open AppendixAProblem

noncomputable instance measurableCN (n : ℕ) : MeasurableSpace (CN n) := borel (CN n)
instance borelCN (n : ℕ) : BorelSpace (CN n) := ⟨rfl⟩

def Quadratic {n : ℕ} (q : CN n → ℝ) : Prop :=
  ∃ (c : ℝ) (l : CN n →L[ℝ] ℝ) (H : CN n →L[ℝ] CN n →L[ℝ] ℝ),
    (∀ v w, H v w = H w v) ∧ ∀ y, q y = c+l y+H y y

def PluriharmonicQuadratic {n : ℕ} (q : CN n → ℝ) : Prop :=
  Quadratic q ∧ ∀ y, mixed q y = 0

noncomputable def energy {n : ℕ} (μ : Measure (CN n)) (K : Set (CN n)) (q : CN n → ℝ) : ℝ :=
  ∫ y in K, q y^2 ∂μ

noncomputable def grad {n : ℕ} (u : CN n → ℝ) (x : CN n) (i : Fin n) : ℂ :=
  ((fderiv ℝ u x (xAxis i):ℂ)-Complex.I*(fderiv ℝ u x (yAxis i):ℂ))/2

noncomputable def A {n : ℕ} (u : CN n → ℝ) (x : CN n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => mixed u x i j+grad u x i*star (grad u x j)/(2*(-u x):ℝ)

noncomputable def B {n : ℕ} (u : CN n → ℝ) (x : CN n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => pure u x i j+grad u x i*grad u x j/(2*(-u x):ℝ)

noncomputable def quotient {n : ℕ} (u : CN n → ℝ) (x : CN n) : Matrix (Fin n) (Fin n) ℂ :=
  (A u x-B u x*((A u x).map star)⁻¹*(B u x).map star)*(A u x)⁻¹

noncomputable def minimumRoot {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t : ℝ | Module.End.HasEigenvalue K.toLin' (t:ℂ)}

def SimpleLeastSpectrum {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) (i : Fin n), IsUnit Q.det ∧
    Q*K*Q⁻¹ = Matrix.diagonal (fun j => (d j:ℂ)) ∧ minimumRoot K = d i ∧
    ∀ j, j ≠ i → d i < d j

def SeparationStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : Measure (CN n)),
    IsFiniteMeasureOnCompacts μ → Measure.IsOpenPosMeasure μ →
    ∀ (K : Set (CN n)), IsCompact K → (interior K).Nonempty →
    ∀ (u : CN n → ℝ) (x : CN n), ContDiffAt ℝ 2 u x →
    ∀ (ε : ℝ), 0 < ε →
    (∀ q : CN n → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε → u x+q x < 0) →
    (∀ q : CN n → ℝ, PluriharmonicQuadratic q → energy μ K q ≤ ε →
      (mixed (fun y => -Real.sqrt (-(u y+q y))) x).PosDef) →
    ∃ q : CN n → ℝ, PluriharmonicQuadratic q ∧ energy μ K q ≤ ε ∧
      (∀ r : CN n → ℝ, PluriharmonicQuadratic r → energy μ K r ≤ ε →
        minimumRoot (quotient (fun y => u y+q y) x) ≤
          minimumRoot (quotient (fun y => u y+r y) x)) ∧
      SimpleLeastSpectrum (quotient (fun y => u y+q y) x)

end PowerConvexityComparator.SeparationProblem
