import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Independent statements for the two paper endpoints.

This file imports only Mathlib. In particular it uses neither a project domain
predicate nor a project differential operator. The second derivatives below
are actual real Frechet derivatives, with the Wirtinger factor 1/4 written out.
The problem file is frozen before the solution adapters are compiled.
-/
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexityComparator.Problem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def StrictDomain (U : Set E) : Prop :=
  ∀ x ∈ closure U, ∀ y ∈ closure U, x ≠ y →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ U

def SmoothBoundary (U : Set E) : Prop :=
  ∀ x ∈ frontier U, ∃ f : E → ℝ, ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧
    fderiv ℝ f x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)

/-- Continuous extensions to the closure of the actual interior derivatives.
No extension of the solution across the boundary is assumed. -/
def ClosedC2 (u : E → ℝ) (U : Set E) : Prop :=
  ∃ D : E → E →L[ℝ] ℝ, ∃ H : E → E →L[ℝ] E →L[ℝ] ℝ,
    ContinuousOn u (closure U) ∧ ContinuousOn D (closure U) ∧
    ContinuousOn H (closure U) ∧
    (∀ x ∈ U, D x = fderiv ℝ u x) ∧
    (∀ x ∈ U, H x = fderiv ℝ (fderiv ℝ u) x)

abbrev CTwo := EuclideanSpace ℂ (Fin 2)

noncomputable def realAxis (i : Fin 2) : CTwo := EuclideanSpace.single i 1
noncomputable def imaginaryAxis (i : Fin 2) : CTwo := Complex.I • realAxis i

noncomputable def mixedHessianTwo (u : CTwo → ℝ) (x : CTwo) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (4 : ℂ)⁻¹ *
    ((fderiv ℝ (fderiv ℝ u) x (realAxis i) (realAxis j) : ℂ) +
     (fderiv ℝ (fderiv ℝ u) x (imaginaryAxis i) (imaginaryAxis j) : ℂ) +
     Complex.I *
       ((fderiv ℝ (fderiv ℝ u) x (realAxis i) (imaginaryAxis j) : ℂ) -
        (fderiv ℝ (fderiv ℝ u) x (imaginaryAxis i) (realAxis j) : ℂ)))

/-- The scalar complex Monge--Ampere equation in complex dimension one. -/
noncomputable def mixedHessianOne (u : ℂ → ℝ) (x : ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) x 1 1 +
    fderiv ℝ (fderiv ℝ u) x Complex.I Complex.I) / 4

def MainStatement : Prop :=
  ∀ (U : Set CTwo), IsOpen U → Bornology.IsBounded U →
    StrictDomain U → SmoothBoundary U →
    ∀ (u : CTwo → ℝ), ContDiffOn ℝ 4 u U → ClosedC2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (mixedHessianTwo u x).PosDef) →
      (∀ x ∈ U, (mixedHessianTwo u x).det = 1) →
      StrictConvexOn ℝ U (fun x => -Real.sqrt (-u x))

def AppendixCStatement : Prop :=
  ∀ (U : Set ℂ), IsOpen U → Bornology.IsBounded U →
    StrictDomain U → SmoothBoundary U →
    ∀ (u : ℂ → ℝ), ContDiffOn ℝ 2 u U → ClosedC2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, mixedHessianOne u x = 1) →
      StrictConvexOn ℝ U (fun x => -Real.sqrt (-u x))

end PowerConvexityComparator.Problem
