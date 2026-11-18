import PowerConvexity.Calculus.UniformNormalizedJetsTwo
import PowerConvexity.Calculus.NormalizedSigmaEstimateTwo
import PowerConvexity.Calculus.SpectralContractionCovariance
import PowerConvexity.Calculus.TakagiNormalizationTwo
import PowerConvexity.Calculus.MinimalEigenvalueContact

/-! # The actual neighborhood inequality sigma_super_harmonic

No normalized jet bound or regular frame selection is a premise. All local
constants follow from the actual C4 solution, strict branch and positive gap.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem modifiedK_normalized_gap_sqrt_two {u : E → ℝ} {x : E}
    (a b : Fin 2 → E) (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd1 : 0 ≤ d 1) (ho : d 1 ≤ d 0) :
    Real.sqrt (eigenDiscriminantTwo (modifiedK a b u x)) = d 0^2-d 1^2 := by
  have hd0 : 0 ≤ d 0 := hd1.trans ho
  have hs : 0 ≤ d 0^2-d 1^2 := by nlinarith
  rw [modifiedK_normalized_diagonal a b d hI hD,eigenDiscriminantTwo_real_diagonal]
  rw [show (1-d 0^2-(1-d 1^2))^2 = (d 0^2-d 1^2)^2 by ring,Real.sqrt_sq_eq_abs,
    abs_of_nonneg hs]

theorem modifiedSigmaTwo_eventually_gradient_estimate (a b : Fin 2 → E)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    {x : E} (hx : x ∈ U) (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      complexLinearized a b u (modifiedSigmaTwo a b u) y ≤
        C*(modifiedSigmaTwo a b u y+‖fderiv ℝ (modifiedSigmaTwo a b u) y‖) := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  obtain ⟨B,hB,hjets⟩ := exists_uniform_normalizedSpectralJetBoundTwo hu4 (hneg x hx) a b (hpos x hx)
  let gap := fun y => Real.sqrt (eigenDiscriminantTwo (modifiedK a b u y))
  have hg : ContinuousAt gap x := Real.continuous_sqrt.continuousAt.comp
    (eigenDiscriminantTwo_contDiffAt (modifiedK_contDiffAt_two hu4 (hneg x hx) a b (hpos x hx))).continuousAt
  have hgp : 0 < gap x := Real.sqrt_pos.mpr hgap
  let δ := gap x/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hn : ∀ᶠ y in 𝓝 x, δ < gap y := hg.eventually (lt_mem_nhds (by change gap x/2 < gap x; linarith))
  refine ⟨normalizedSigmaCoefficientTwo B δ,
    normalizedSigmaCoefficientTwo_nonneg (by linarith) hδ,?_⟩
  filter_upwards [hU.mem_nhds hx,hjets,hn] with y hy hj hyδ
  have hy4 := hu.contDiffAt (hU.mem_nhds hy)
  have hy2 : ContDiffAt ℝ 2 u y := hy4.of_le (by norm_num)
  have hygap : 0 < eigenDiscriminantTwo (modifiedK a b u y) := Real.sqrt_pos.mp (hδ.trans hyδ)
  obtain ⟨Q,d,hQ,hd1,ho,hI,hD,_⟩ := exists_modified_takagi_frame_two hy2 (hneg y hy) a b (hpos y hy)
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hA' : ∀ z ∈ U, (complexHessian a' b' u z).PosDef := by
    intro z hz
    exact (complexHessian_posDef_complexFrame_iff
      ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) Q hQ a b).mpr (hpos z hz)
  have hsigma : modifiedSigmaTwo a' b' u y = modifiedSigmaTwo a b u y :=
    modifiedSigmaTwo_complexFrame hy2 (hneg y hy) Q hQ a b
  have hs0 : 0 ≤ modifiedSigmaTwo a' b' u y := by rw [hsigma]; exact hnonneg y hy
  have hκ : gap y = d 0^2-d 1^2 := by
    have he := modifiedK_normalized_gap_sqrt_two a' b' d hI hD hd1 ho
    dsimp only [a',b'] at he
    rw [modifiedSigmaTwo_gap_complexFrame hy2 (hneg y hy) Q hQ a b] at he
    exact he
  have hd0 : 0 ≤ d 0 := hd1.trans ho
  have horder : d 1 < d 0 := by
    by_contra hh
    have he : d 1 = d 0 := le_antisymm ho (le_of_not_gt hh)
    rw [he,sub_self] at hκ
    linarith
  have hσ := (normalized_spectrumTwo_data a' b' d hI hD hd0 hd1 horder).1
  have hdle : d 0 ≤ 1 := by nlinarith
  have hj' := hj Q d hQ hI hD hd0 hdle
  have hden : δ ≤ d 0^2-d 1^2 := by rw [← hκ]; exact hyδ.le
  have ht := constantDensity_complexFrame hU (hu.of_le (by norm_num)) Q a b ρ hdet
  have he := modifiedSigmaTwo_normalized_gradient_estimate hU hu a' b'
    (transformedDensity_ne_zero Q hQ hρ) ht hneg hA' hy d hI hD hd0 hd1 horder hs0 hB hδ hden hj'
  dsimp only [a',b'] at he
  rw [modifiedSigmaTwo_contraction_complexFrame hU hu a b hneg hpos hy hygap Q hQ,
    modifiedSigmaTwo_complexFrame hy2 (hneg y hy) Q hQ a b,
    modifiedSigmaTwo_fderiv_complexFrame hU (hu.of_le (by norm_num)) a b hneg hy Q hQ] at he
  exact he

end PowerConvexity
