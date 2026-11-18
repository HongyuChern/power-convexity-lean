import PowerConvexity.Calculus.ModifiedResidualEvaluation

/-! # The fully evaluated actual modified Schur contraction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `upqmpq` after all four constant-density residual evaluations. This exact
identity is valid before Takagi normalization or error estimates. -/
theorem modifiedSchur_LM_const_evaluated {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (B y).map star
    let Am := modifiedA a b u
    let Bm := modifiedB a b u
    let Hm := fun y => (Am y).map star
    let Cm := fun y => (Bm y).map star
    let W := (A x)⁻¹
    let R := (H x)⁻¹
    let T := (Hm x)⁻¹
    let h := (powerWeight (u x) : ℂ)
    let g := complexGradient a b u x
    let XB := fun q => matrixDZ (a q) (-b q) B x
    let XH := fun q => matrixDZ (a q) (-b q) H x
    let YC := fun p => matrixDZ (a p) (b p) C x
    let YH := fun p => matrixDZ (a p) (b p) H x
    let PB := modificationBbar h g (Am x)
    let PH := fun q => (modificationAz h g (Am x) (Bm x) q).map star
    let QC := fun p => (PB p).map star
    let QH := fun p => (modificationAbar h g (Am x) (Bm x) p).map star
    let SA := modificationASecond h g (Am x) (Bm x)
    let SB := modificationBSecond h g (Am x) (Bm x)
    let SH := fun p q => (SA q p).map star
    let SC := fun p q => (SB q p).map star
    matrixL a b u (modifiedSchur a b u) x =
      residualEvaluation W R T XB YC PB QC SA +
      Bm x * T * residualEvaluation W R T XH YH PH QH SH * T * Cm x -
      residualEvaluation W R T XB YH PB QH SB * T * Cm x -
      Bm x * T * residualEvaluation W R T XH YC PH QC SC -
      contract W (fun p q => modifiedCompensatedHessian a b u p x * T *
        (modifiedCompensatedHessian a b u q x).conjTranspose) := by
  have he := modified_four_residuals_const hU hu a b hρ hdet hx (hneg x hx)
  have hm := modifiedSchur_LM_residual hU hu a b hneg hpos hx
  dsimp only at he hm ⊢
  simp only [matrixL] at he
  simp only [contract_sub] at hm
  rw [he.1, he.2.1, he.2.2.1, he.2.2.2] at hm
  exact hm

end PowerConvexity
