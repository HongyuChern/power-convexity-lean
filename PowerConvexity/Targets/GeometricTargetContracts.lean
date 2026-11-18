import PowerConvexity.Analysis.StrictBoundaryChords
import PowerConvexity.Targets.AppendixCTargetContract
import PowerConvexity.Targets.MainTwoTargetContract

/-! # Target contracts with strictness of the domain checked at boundary endpoints

These are consequences of the earlier, weaker geometric hypotheses. The older
compiled statements remain valid; their open-set StrictConvex parameter was only
convexity. No additional paper endpoint is counted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem appendixC_geometric_main_strictConvexOn
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hchords : HasStrictBoundaryChords U)
    (hsmooth : ∀ x ∈ frontier U, ∃ f : ℂ → ℝ, ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧
      fderiv ℝ f x ≠ 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
    {u : ℂ → ℝ} (hu2 : ContDiffOn ℝ 2 u U) (hJ : Nonempty (ClosureC2Jet u U))
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (hdet : ∀ x ∈ U, (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).det = 1) :
    StrictConvexOn ℝ U (fun y => -Real.sqrt (-u y)) :=
  appendixC_main_strictConvexOn hU hbounded (strictBoundaryChords_mathlib_strictConvex hU hchords)
    hsmooth ⟨hu2,hJ⟩ hboundary hdet

section Two
variable {U : Set (EuclideanSpace ℂ (Fin 2))}
  (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hchords : HasStrictBoundaryChords U)
  (hsmooth : ∀ x ∈ frontier U, ∃ f : EuclideanSpace ℂ (Fin 2) → ℝ,
    ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
    (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
  {u : EuclideanSpace ℂ (Fin 2) → ℝ}
  (hu4 : ContDiffOn ℝ 4 u U) (hJ : Nonempty (ClosureC2Jet u U))
  (hboundary : ∀ x ∈ frontier U, u x = 0)
  (hpsh : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) u x).PosDef)
  (hdet : ∀ x ∈ U, (complexHessian standardComplexTwoBasis
    (fun j => Complex.I • standardComplexTwoBasis j) u x).det = 1)
include hU hbounded hchords hsmooth hu4 hJ hboundary hpsh hdet

theorem mainTwo_geometric_target_nonstrict_chord :
    ∀ x ∈ closure U, ∀ y ∈ closure U, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) ≤
        a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) :=
  mainTwo_target_nonstrict_chord hU hbounded (strictBoundaryChords_mathlib_strictConvex hU hchords)
    hsmooth hu4 hJ hboundary hpsh hdet

theorem mainTwo_geometric_target_strict_chord_of_zero_locus_gap
    (hgap : ∀ x ∈ U, modifiedSigmaTwo standardComplexTwoBasis
        (fun j => Complex.I • standardComplexTwoBasis j) u x = 0 →
      0 < eigenDiscriminantTwo (modifiedK standardComplexTwoBasis
        (fun j => Complex.I • standardComplexTwoBasis j) u x)) :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ∀ a b : ℝ,
      0 < a → 0 < b → a+b = 1 →
      -Real.sqrt (-u (a • x+b • y)) <
        a*(-Real.sqrt (-u x))+b*(-Real.sqrt (-u y)) :=
  mainTwo_target_strict_chord_of_zero_locus_gap hU hbounded
    (strictBoundaryChords_mathlib_strictConvex hU hchords) hsmooth hu4 hJ hboundary hpsh hdet hgap

end Two
end PowerConvexity
