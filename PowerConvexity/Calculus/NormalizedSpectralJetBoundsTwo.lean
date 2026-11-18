import PowerConvexity.Calculus.NormalizedSchurErrorTwo
import PowerConvexity.Calculus.NormalizedDefectEstimate
import PowerConvexity.Calculus.SpectralContractionExactTwo
import PowerConvexity.Algebra.ContactVectorBoundsTwo

/-! # Explicit actual jet hypotheses and the two spectral-vector estimates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This predicate lists actual finite jet bounds; it contains no PDE estimate. -/
def normalizedSpectralJetBoundTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) (B : ℝ) : Prop :=
  readingTableJetBoundTwo a b u x B ∧
  matrixEntryBoundTwo (skewThirdHessian a b u 0 x) B ∧
  (∀ p s, ‖modifiedCompensatedHessian a b u p x 0 s‖ ≤ B) ∧
  ‖(powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))‖ ≤ B ∧
  (∀ p s, ‖normalizedThirdRemainder a b u 0 x p s‖ ≤ B) ∧
  (∀ p i j, ‖dz (a p) (b p) (fun y => modifiedA a b u y i j) x‖ ≤ B) ∧
  (∀ p i j, ‖dz (a p) (b p) (fun y => star (modifiedB a b u y i j)) x‖ ≤ B) ∧
  (∀ p q, ‖dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedA a b u y 0 0)) x‖ ≤ B) ∧
  (∀ p, (‖a p‖+‖b p‖)/2 ≤ B)

theorem modifiedPencilFirstVectorTwo_error_bounds {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) {B : ℝ} (hB : 0 ≤ B)
    (hjets : normalizedSpectralJetBoundTwo a b u x B) (p : Fin 2) :
    let W := skewThirdHessian a b u 0 x
    let D : Matrix (Fin 2) (Fin 2) ℂ := fun q s => modifiedCompensatedHessian a b u q x 0 s
    let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
    ‖modifiedPencilFirstVectorTwo a b u x 0 1 p-contactUpperVectorTwo W D τ (d 1) p‖ ≤
      2*B*modifiedSigmaTwo a b u x ∧
    ‖modifiedPencilFirstVectorTwo a b u x 1 0 p-contactLowerVectorTwo W D τ (d 1) p‖ ≤
      9*B*modifiedSigmaTwo a b u x ∧
    ‖modifiedPencilFirstVectorTwo a b u x 0 1 p‖ ≤ 12*B ∧
    ‖modifiedPencilFirstVectorTwo a b u x 1 0 p‖ ≤ 12*B ∧
    ‖contactUpperVectorTwo W D τ (d 1) p‖ ≤ 12*B ∧
    ‖contactLowerVectorTwo W D τ (d 1) p‖ ≤ 12*B := by
  obtain ⟨_,hW,hDb,hτ,hR,hAb,hCb,_,_⟩ := hjets
  obtain ⟨hσ,_,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have ht1 : d 0 ≤ 1 := by nlinarith
  have hb1 : d 1 ≤ 1 := ho.le.trans ht1
  have hσ1 : modifiedSigmaTwo a b u x ≤ 1 := by nlinarith [sq_nonneg (d 0)]
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun q s => modifiedCompensatedHessian a b u q x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  let V := contactUpperVectorTwo W D τ (d 1) p
  let H := contactLowerVectorTwo W D τ (d 1) p
  have hnorm := contactVector_norm_bounds_two hB hd1 hb1 W D τ hW hDb hτ p
  have hrow : modifiedPencilFirstVectorTwo a b u x 0 1 p = V+
      (1-(d 0:ℂ))*normalizedThirdRemainder a b u 0 x p 1-
      (modifiedSigmaTwo a b u x:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y 0 1) x := by
    unfold modifiedPencilFirstVectorTwo
    rw [modifiedSchur_dz_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) a b (hA x hx) d hI hD 0 1 p]
    rfl
  let R := -H+(d 1:ℂ)*(d 0:ℂ)*normalizedThirdRemainder a b u 0 x p 1+
    (1+(d 0:ℂ))*(dz (a p) (b p) (fun y => modifiedA a b u y 1 0) x-
      (d 1:ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y 0 1)) x)
  have hcol : modifiedPencilFirstVectorTwo a b u x 1 0 p = H+(1-(d 0:ℂ))*R-
      (modifiedSigmaTwo a b u x:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y 1 0) x := by
    unfold modifiedPencilFirstVectorTwo
    rw [modifiedSchur_column_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) a b (hA x hx) d hI hD 0 1 p]
    rfl
  have hRn : ‖R‖ ≤ 8*B := schurLowerRemainder_norm_bound hB hd0 ht1 hd1 hb1 H _ _ _
    hnorm.2 (hR p 1) (hAb p 1 0) (hCb p 0 1)
  have he₁ : ‖modifiedPencilFirstVectorTwo a b u x 0 1 p-V‖ ≤ 2*B*modifiedSigmaTwo a b u x := by
    convert schurVector_sigma_error_bound hB (by norm_num : (0:ℝ) ≤ 1) hd0 ht1 hσ _ V _ _
      (by simpa using hR p 1) (hAb p 0 1) hrow using 1 <;> norm_num
  have he₂ : ‖modifiedPencilFirstVectorTwo a b u x 1 0 p-H‖ ≤ 9*B*modifiedSigmaTwo a b u x := by
    convert schurVector_sigma_error_bound hB (by norm_num : (0:ℝ) ≤ 8) hd0 ht1 hσ _ H R _
      hRn (hAb p 1 0) hcol using 1 <;> norm_num
  refine ⟨he₁,he₂,?_,?_,?_,?_⟩
  · have hh := vector_norm_le_of_sigma_error hB (by norm_num : (0:ℝ) ≤ 2) hσ0 hσ1 _ V hnorm.1 he₁
    exact hh.trans (by nlinarith)
  · convert vector_norm_le_of_sigma_error hB (by norm_num : (0:ℝ) ≤ 9) hσ0 hσ1 _ H hnorm.2 he₂ using 1 <;> norm_num
  · exact hnorm.1.trans (by nlinarith)
  · exact hnorm.2.trans (by nlinarith)

end PowerConvexity
