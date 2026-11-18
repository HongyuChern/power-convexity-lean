import PowerConvexity.Calculus.ModifiedContactSpectrumTwo
import PowerConvexity.Calculus.ModifiedContactContractionTwo
import PowerConvexity.Calculus.NormalizedWeight
import PowerConvexity.Algebra.FullQuadraticCompletionTwo

/-! # final_fullQ for actual derivatives at a zero critical contact

This is an exact pointwise identity. A neighborhood differential inequality
with C(sigma+norm Dsigma) is a separate theorem and is not inferred here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_contact_contraction_eq_quadratic {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) =
    contactFullQuadraticTwo (complexHessian a b u x)⁻¹ (skewThirdHessian a b u 0 x)
      (fun p s => modifiedCompensatedHessian a b u p x 0 s)
      ((powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))) (d 1) := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun p s => modifiedCompensatedHessian a b u p x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  have hrow (p : Fin 2) : dz (a p) (b p) (fun y => modifiedSchur a b u y 0 1) x =
      contactUpperVectorTwo W D τ (d 1) p :=
    modifiedSchur_dz_contact_row (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD 0 1 p hd
  have hcol (p : Fin 2) : dz (a p) (b p) (fun y => modifiedSchur a b u y 1 0) x =
      contactLowerVectorTwo W D τ (d 1) p :=
    modifiedSchur_dz_contact_column (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD 0 1 p hd
  have hmix (p q : Fin 2) := modifiedSigmaTwo_contact_mixed hU hu a b hneg hA hx d hI hD hd hd1 h1 hc p q
  have hl := modifiedSchur_LM_contact_two hU hu a b hρ hdet hneg hA hx d hI hD hd
  change matrixL a b u (modifiedSchur a b u) x 0 0 =
    typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace-∑ s,weightedSquare G (fun p => D p s) at hl
  change (∑ p,∑ q,G q p*dz (a q) (-b q)
    (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) = contactFullQuadraticTwo G W D τ (d 1)
  simp_rw [hmix,hrow,hcol]
  unfold contactFullQuadraticTwo
  rw [← hl]
  simp only [matrixL,contract,Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,
    Pi.smul_apply,smul_eq_mul,matrixDZ,weightedSquare,Fin.sum_univ_two]
  dsimp only [G]
  push_cast
  ring

theorem modifiedSigmaTwo_contact_contraction_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x).re ≤ 0 := by
  rw [modifiedSigmaTwo_contact_contraction_eq_quadratic hU hu a b hρ hdet hneg hA hx d hI hD hd hd1 h1 hc]
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hG := originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hA x hx)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  rw [hG] at ht ⊢
  apply contactFullQuadraticTwo_nonpos _ _ (skewThirdHessian_conjTranspose hu3 a b 0) _ _ _
  · have hs : d 1^2 < (1:ℝ)^2 := (sq_lt_sq₀ hd1 zero_le_one).mpr h1
    exact sub_pos.mpr (by simpa only [one_pow] using hs)
  · exact ht
  · exact modifiedCompensated_contact_first_column hU hu a b hneg hA hx d hI hD hd hd1 h1 hc

/-- Frozen final_fullQ as an exact actual-derivative identity at zero contact. -/
theorem modifiedSigmaTwo_final_fullQ_contact {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) =
      (Complex.normSq (skewThirdHessian a b u 0 x).trace:ℂ)-
      (∑ p,∑ s,(Complex.normSq (skewThirdHessian a b u 0 x p s):ℂ))-
      2*weightedSquare (complexHessian a b u x)⁻¹
        (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y 1 0) x)/
      (1-(d 1:ℂ)^2) := by
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun p s => modifiedCompensatedHessian a b u p x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hG : (complexHessian a b u x)⁻¹ = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hA x hx)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  rw [hG] at ht
  have hμ : 1-(d 1:ℂ)^2 ≠ 0 := by
    have hs : d 1^2 < (1:ℝ)^2 := (sq_lt_sq₀ hd1 zero_le_one).mpr h1
    have hp : 0 < 1-d 1^2 := sub_pos.mpr (by simpa only [one_pow] using hs)
    exact_mod_cast ne_of_gt hp
  have hD0 : ∀ p,D p 0 = W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0 :=
    modifiedCompensated_contact_first_column hU hu a b hneg hA hx d hI hD hd hd1 h1 hc
  have hcol : (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y 1 0) x) =
      contactLowerVectorTwo W D τ (d 1) := by
    funext p
    exact modifiedSchur_dz_contact_column (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD 0 1 p hd
  rw [modifiedSigmaTwo_contact_contraction_eq_quadratic hU hu a b hρ hdet hneg hA hx d hI hD hd hd1 h1 hc,hG]
  exact (contactFullQuadraticTwo_eq W D (skewThirdHessian_conjTranspose hu3 a b 0) r τ (d 1) hμ ht hD0).trans
    (by rw [← hcol])

end PowerConvexity
