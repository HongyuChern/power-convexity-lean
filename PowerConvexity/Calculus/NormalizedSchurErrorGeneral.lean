import PowerConvexity.Calculus.NormalizedSchurResidualGeneral

/-! # Actual normalized ReadingTable remainder in every finite dimension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite bounds on the actual original jets entering ReadingTable. -/
def readingTableJetBoundGeneral (a b : ι → E) (u : E → ℝ) (x : E) (B : ℝ) : Prop :=
  matrixEntryBoundGeneral (complexHessian a b u x)⁻¹ B ∧
  ‖(powerWeight (u x):ℂ)‖ ≤ B ∧ (∀ i, ‖complexGradient a b u x i‖ ≤ B) ∧
  (∀ q, matrixEntryBoundGeneral (matrixDZ (a q) (-b q) (pureHessian a b u) x) B) ∧
  (∀ q, matrixEntryBoundGeneral (matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x) B) ∧
  (∀ p, matrixEntryBoundGeneral (matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x) B) ∧
  (∀ p, matrixEntryBoundGeneral (matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x) B)

theorem actualReadingTable_takagi_error_general (a b : ι → E) (u : E → ℝ) (x : E)
    (d : ι → ℝ) (i : ι) {B σ : ℝ} (hB : 1 ≤ B)
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1)
    (hσ : σ = 1-d i^2) (hjets : readingTableJetBoundGeneral a b u x B) :
    ‖readingTableCombinationTwo (d i) (fun l => actualReadingTableGeneral a b u x d l i i)-
      readingTableCombinationTwo 1 (fun l =>
        actualReadingTableGeneral a b u x (Function.update d i 1) l i i)‖ ≤
      readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5*σ := by
  obtain ⟨hG,hh,hg,hXB,hXH,hYC,hYH⟩ := hjets
  exact readingTableCombination_takagi_error_general hB d i hd0 hd1 hσ _ _ _ _ _ _ _
    hG hh hg hXB hXH hYC hYH

theorem modifiedSchur_LM_normalized_error_general {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : ι → ℝ) (i : ι)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    {B σ : ℝ} (hB : 1 ≤ B) (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1)
    (hσ : σ = 1-d i^2) (hjets : readingTableJetBoundGeneral a b u x B) :
    ‖matrixL a b u (modifiedSchur a b u) x i i-
      (typeIQuadratic (complexHessian a b u x)⁻¹ (skewThirdHessian a b u i x)+
        (Complex.normSq ((powerWeight (u x) : ℂ)*
          (complexGradient a b u x i-star (complexGradient a b u x i))) : ℂ)*
          ((complexHessian a b u x)⁻¹).trace-
        ∑ s, weightedSquare (complexHessian a b u x)⁻¹
          (fun p => modifiedCompensatedHessian a b u p x i s))‖ ≤
      readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5*σ := by
  have he := actualReadingTable_takagi_error_general a b u x d i hB hd0 hd1 hσ hjets
  have hc := actualReadingTableGeneral_contact_value
    ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) a b
    (Filter.Eventually.mono (hU.mem_nhds hx) hdet) (Function.update d i 1) i (by simp)
  rw [hc] at he
  rw [modifiedSchur_LM_normalized_general hU hu a b hρ hdet hneg hpos hx d i hI hD]
  simpa only [sub_sub_sub_cancel_right] using he

end PowerConvexity
