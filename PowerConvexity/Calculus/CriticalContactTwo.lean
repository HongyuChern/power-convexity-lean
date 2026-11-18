import PowerConvexity.Calculus.FinalContactTwo
import PowerConvexity.Calculus.SpectralContractionCovariance
import PowerConvexity.Calculus.TakagiNormalizationTwo

/-! # Coordinate-free zero-contact sign for the actual lowest-root field

The pointwise sign is proved on the simple branch. No neighborhood maximum
principle is asserted from this pointwise fact alone.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_critical_zero_contraction_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hzero : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x).re ≤ 0 := by
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  obtain ⟨Q,d,hQ,hd1,ho,hI,hD,hK⟩ := exists_modified_takagi_frame_two hu2 (hneg x hx) a b (hA x hx)
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hA' : ∀ y ∈ U, (complexHessian a' b' u y).PosDef := by
    intro y hy
    exact (complexHessian_posDef_complexFrame_iff
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) Q hQ a b).mpr (hA y hy)
  have hz : modifiedSigmaTwo a' b' u x = 0 := by
    rw [modifiedSigmaTwo_complexFrame hu2 (hneg x hx) Q hQ a b,hzero]
  have hg : 0 < eigenDiscriminantTwo (modifiedK a' b' u x) := by
    rw [modifiedSigmaTwo_gap_complexFrame hu2 (hneg x hx) Q hQ a b]
    exact hgap
  have hd0 : 0 ≤ d 0 := hd1.trans ho
  have hsq : 1-d 0^2 ≤ 1-d 1^2 := by nlinarith
  have hz' := hz
  unfold modifiedSigmaTwo at hz'
  rw [hK,lowerEigenvalueTwo_real_diagonal,min_eq_left hsq] at hz'
  have hd : d 0 = 1 := by nlinarith
  have hle : d 1 ≤ 1 := by simpa only [hd] using ho
  have h1 : d 1 < 1 := by
    apply lt_of_le_of_ne hle
    intro he
    rw [hK,eigenDiscriminantTwo_real_diagonal] at hg
    norm_num [hd,he] at hg
  have hc' : fderiv ℝ (modifiedSigmaTwo a' b' u) x = 0 := by
    rw [modifiedSigmaTwo_fderiv_complexFrame hU (hu.of_le (by norm_num)) a b hneg hx Q hQ]
    exact hc
  have ht := constantDensity_complexFrame hU (hu.of_le (by norm_num)) Q a b ρ hdet
  have hp := modifiedSigmaTwo_contact_contraction_nonpos hU hu a' b'
    (transformedDensity_ne_zero Q hQ hρ) ht hneg hA' hx d hI hD hd hd1 h1 hc'
  dsimp only [a',b'] at hp
  rw [modifiedSigmaTwo_contraction_complexFrame hU hu a b hneg hA hx hgap Q hQ] at hp
  exact hp

theorem modifiedSigmaTwo_localMin_zero_contraction_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hzero : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hm : IsLocalMin (modifiedSigmaTwo a b u) x) :
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x).re ≤ 0 :=
  modifiedSigmaTwo_critical_zero_contraction_nonpos hU hu a b hρ hdet hneg hA hx hzero hgap hm.fderiv_eq_zero

end PowerConvexity
