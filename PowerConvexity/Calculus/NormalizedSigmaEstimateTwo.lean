import PowerConvexity.Calculus.NormalizedLeadingQuadraticTwo
import PowerConvexity.Calculus.NormalizedLinearRemaindersTwo
import PowerConvexity.Algebra.SpectralWeightedErrorTwo

/-! # The actual simple-root PDE estimate under explicit normalized jet bounds

This theorem is pointwise. Establishing the same B and delta in a neighborhood
for arbitrary pointwise Takagi frames is a further analytic obligation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def normalizedSigmaCoefficientTwo (B δ : ℝ) : ℝ :=
  768*B^5+72*B^3+4*B^2+1056*B^3/δ+32*B^3

theorem normalizedSigmaCoefficientTwo_nonneg {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) :
    0 ≤ normalizedSigmaCoefficientTwo B δ := by unfold normalizedSigmaCoefficientTwo; positivity

theorem modifiedSigmaTwo_normalized_gradient_estimate_explicit {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 < δ)
    (hgap : δ ≤ d 0^2-d 1^2) (hjets : normalizedSpectralJetBoundTwo a b u x B) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x).re ≤
      (768*B^5+72*B^3+4*B^2+1056*B^3/δ)*modifiedSigmaTwo a b u x+
        32*B^3*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun p s => modifiedCompensatedHessian a b u p x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  let σ := modifiedSigmaTwo a b u x
  let κ := d 0^2-d 1^2
  let μ := 1-d 1^2
  let V := contactUpperVectorTwo W D τ (d 1)
  let H := contactLowerVectorTwo W D τ (d 1)
  let F := typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace-
    ∑ s,weightedSquare G (fun p => D p s)
  let LM := matrixL a b u (modifiedSchur a b u) x 0 0
  let LA := matrixL a b u (modifiedA a b u) x 0 0
  let T := spectralGradientCrossTwo G
    (fun p => dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ)) x)
    (fun p => dz (a p) (b p) (fun y => modifiedA a b u y 0 0) x)
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨hσ,_,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have ht1 : d 0 ≤ 1 := by nlinarith
  have hb1 : d 1 ≤ 1 := ho.le.trans ht1
  have hκμ : κ ≤ μ := by dsimp [κ,μ]; nlinarith
  have hLM : ‖LM-F‖ ≤ 768*B^5*σ :=
    modifiedSchur_LM_normalized_error_two hU hu a b hρ hdet hneg hA hx d hI hD
      hB hd0 ht1 hd1 hb1 hσ hjets.1
  have hLMre : LM.re ≤ F.re+768*B^5*σ := by
    have hh := (Complex.re_le_norm (LM-F)).trans hLM
    rw [Complex.sub_re] at hh
    linarith
  have hvec := modifiedPencilFirstVectorTwo_error_bounds hU hu a b hneg hA hx d hI hD hd0 hd1 ho hσ0 hB0 hjets
  have hGpos : G.PosSemidef := (hA x hx).inv.posSemidef
  have hsq := two_spectral_squares_error_bound G hGpos
    (modifiedPencilFirstVectorTwo a b u x 0 1) (modifiedPencilFirstVectorTwo a b u x 1 0) V H
    hB0 hσ0 hδ hgap hκμ (fun p q => hjets.1.1 q p)
    (fun p => (hvec p).2.2.1) (fun p => (hvec p).2.2.2.1)
    (fun p => (hvec p).2.2.2.2.1) (fun p => (hvec p).2.2.2.2.2)
    (fun p => (hvec p).1) (fun p => (hvec p).2.1)
  have hQ := modifiedSigmaTwo_leadingQuadratic_bound hU hu a b hdet hneg hA hx d hI hD
    hd0 hd1 ho hσ0 hB0 hjets
  have hQeq : (contactFullQuadraticTwo G W D τ (d 1)).re =
      F.re-(weightedSquare G V/(μ:ℂ)).re-(weightedSquare G H/(μ:ℂ)).re := by
    unfold contactFullQuadraticTwo
    change ((F-weightedSquare G V/(1-(d 1:ℂ)^2))-weightedSquare G H/(1-(d 1:ℂ)^2)).re = _
    rw [show 1-(d 1:ℂ)^2 = (μ:ℂ) by dsimp [μ]; push_cast; rfl]
    simp only [Complex.sub_re]
  change (contactFullQuadraticTwo G W D τ (d 1)).re ≤ _ at hQ
  rw [hQeq] at hQ
  obtain ⟨hLA,hT⟩ := modifiedSigmaTwo_linear_remainders_bounds hU hu a b hneg hA hx d hI hD
    hd0 hd1 ho hσ0 hB0 hjets
  have hLAre : -((σ:ℂ)*LA).re ≤ 4*B^2*σ := by
    have hh := Complex.re_le_norm (-((σ:ℂ)*LA))
    simp only [Complex.neg_re,norm_neg] at hh
    exact hh.trans hLA
  have hTre : -T.re ≤ 8*B^3*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
    have hh := Complex.re_le_norm (-T)
    simp only [Complex.neg_re,norm_neg] at hh
    exact hh.trans hT
  rw [modifiedSigmaTwo_contraction_normalized_exact hU hu a b hneg hA hx d hI hD hd0 hd1 ho]
  change (LM-(σ:ℂ)*LA-T-weightedSquare G (modifiedPencilFirstVectorTwo a b u x 0 1)/(κ:ℂ)-
    weightedSquare G (modifiedPencilFirstVectorTwo a b u x 1 0)/(κ:ℂ)).re ≤ _
  simp only [Complex.sub_re]
  have he : 1056*B^3*σ/δ = (1056*B^3/δ)*σ := by ring
  rw [he] at hsq
  dsimp only [σ] at hLMre hsq hQ hLAre
  nlinarith

theorem modifiedSigmaTwo_normalized_gradient_estimate {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 < δ)
    (hgap : δ ≤ d 0^2-d 1^2) (hjets : normalizedSpectralJetBoundTwo a b u x B) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x).re ≤
      normalizedSigmaCoefficientTwo B δ*
        (modifiedSigmaTwo a b u x+‖fderiv ℝ (modifiedSigmaTwo a b u) x‖) := by
  refine (modifiedSigmaTwo_normalized_gradient_estimate_explicit hU hu a b hρ hdet hneg hA hx d hI hD
    hd0 hd1 ho hσ0 hB hδ hgap hjets).trans ?_
  have hB0 : 0 ≤ B := by linarith
  have h₁ : 0 ≤ 768*B^5+72*B^3+4*B^2+1056*B^3/δ := by positivity
  have h₂ : 0 ≤ 32*B^3 := by positivity
  unfold normalizedSigmaCoefficientTwo
  nlinarith [mul_nonneg h₁ (norm_nonneg (fderiv ℝ (modifiedSigmaTwo a b u) x)),mul_nonneg h₂ hσ0]

end PowerConvexity
