import PowerConvexity.Calculus.NormalizedSchurResidualTwo

/-! # A quantitative ReadingTable error for the actual modified Schur matrix -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite bounds on the actual original jets entering ReadingTable. -/
def readingTableJetBoundTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) (B : ℝ) : Prop :=
  matrixEntryBoundTwo (complexHessian a b u x)⁻¹ B ∧
  ‖(powerWeight (u x):ℂ)‖ ≤ B ∧ (∀ i, ‖complexGradient a b u x i‖ ≤ B) ∧
  (∀ q, matrixEntryBoundTwo (matrixDZ (a q) (-b q) (pureHessian a b u) x) B) ∧
  (∀ q, matrixEntryBoundTwo (matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x) B) ∧
  (∀ p, matrixEntryBoundTwo (matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x) B) ∧
  (∀ p, matrixEntryBoundTwo (matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x) B)

theorem actualReadingTableTwo_takagi_error (a b : Fin 2 → E) (u : E → ℝ) (x : E)
    (d : Fin 2 → ℝ) {B σ : ℝ} (hB : 1 ≤ B)
    (hd0 : 0 ≤ d 0) (hd1 : d 0 ≤ 1) (he0 : 0 ≤ d 1) (he1 : d 1 ≤ 1)
    (hσ : σ = 1-(d 0)^2) (hjets : readingTableJetBoundTwo a b u x B) :
    ‖readingTableCombinationTwo (d 0) (fun k => actualReadingTableTwo a b u x d k 0 0)-
      readingTableCombinationTwo 1 (fun k => actualReadingTableTwo a b u x ![1,d 1] k 0 0)‖ ≤
      768*B^5*σ := by
  obtain ⟨hG,hh,hg,hXB,hXH,hYC,hYH⟩ := hjets
  have hcast (e : Fin 2 → ℝ) : (fun i => (e i:ℂ)) = ![(e 0:ℂ),(e 1:ℂ)] := by
    funext i
    fin_cases i <;> rfl
  dsimp only [actualReadingTableTwo]
  rw [hcast d,hcast ![1,d 1]]
  exact readingTableCombinationTwo_takagi_error hB hd0 hd1 he0 he1 hσ _ _ _ _ _ _ _
    hG hh hg hXB hXH hYC hYH

theorem modifiedSchur_LM_normalized_error_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    {B σ : ℝ} (hB : 1 ≤ B)
    (hd0 : 0 ≤ d 0) (hd1 : d 0 ≤ 1) (he0 : 0 ≤ d 1) (he1 : d 1 ≤ 1)
    (hσ : σ = 1-(d 0)^2) (hjets : readingTableJetBoundTwo a b u x B) :
    ‖matrixL a b u (modifiedSchur a b u) x 0 0-
      (typeIQuadraticTwo (complexHessian a b u x)⁻¹ (skewThirdHessian a b u 0 x)+
        (Complex.normSq ((powerWeight (u x):ℂ)*
          (complexGradient a b u x 0-star (complexGradient a b u x 0))):ℂ)*
          ((complexHessian a b u x)⁻¹).trace-
        ∑ s,weightedSquare (complexHessian a b u x)⁻¹
          (fun p => modifiedCompensatedHessian a b u p x 0 s))‖ ≤ 768*B^5*σ := by
  have he := actualReadingTableTwo_takagi_error a b u x d hB hd0 hd1 he0 he1 hσ hjets
  have hc := actualReadingTableTwo_contact_value
    ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) a b
    (Filter.Eventually.mono (hU.mem_nhds hx) hdet) ![1,d 1] (by rfl)
  rw [hc] at he
  rw [modifiedSchur_LM_normalized_two hU hu a b hρ hdet hneg hpos hx d hI hD]
  simpa only [sub_sub_sub_cancel_right] using he

end PowerConvexity
