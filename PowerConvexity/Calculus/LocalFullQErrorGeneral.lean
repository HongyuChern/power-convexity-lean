import PowerConvexity.Calculus.UniformNormalizedQJetsGeneral
import PowerConvexity.Calculus.NormalizedFullQErrorGeneral
import PowerConvexity.Calculus.LinearizationCovariance

/-! # A common-neighborhood full-Q estimate for the same physical potential

All derivative bounds are obtained from C4 regularity before selecting the
point or the frame. The displayed delta is a quantitative simple-root gap;
its role is kept distinct from the analytic jet bounds.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem modifiedSigma_eventuallyEq_complexFrame_general [Nonempty ι]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0) {x : E} (hx : x ∈ U)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) :
    modifiedSigma (complexFrameReal Q a b) (complexFrameImag Q a b) u =ᶠ[𝓝 x]
      modifiedSigma a b u := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact modifiedSigma_complexFrame (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) Q hQ a b

theorem modifiedSigma_fullQ_error_common_neighborhood_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (d : ι → ℝ),
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y = Matrix.diagonal (fun j => (d j : ℂ)) →
      (∀ j, 0 ≤ d j) → (∀ j, j ≠ i → δ ≤ d i^2-d j^2) →
      0 ≤ modifiedSigma a b u y →
      ‖(∑ p, ∑ q, (complexHessian a b u y)⁻¹ q p*
        dz (a q) (-b q) (dz (a p) (b p) (fun z => (modifiedSigma a b u z : ℂ))) y)-
        normalizedFullQExpressionGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u y d i‖ ≤
      normalizedFullQErrorCoefficientGeneral (Fintype.card ι) (Fintype.card {j : ι // j ≠ i}) B δ*
        (modifiedSigma a b u y+‖fderiv ℝ (modifiedSigma a b u) y‖) := by
  letI : Nonempty ι := ⟨i⟩
  obtain ⟨B,hB,hjets⟩ := normalizedQJetBoundGeneral_eventually hU hu hneg a b hpos hx
  refine ⟨B,hB,?_⟩
  filter_upwards [hjets,hU.mem_nhds hx] with y hy hyU
  intro Q hQ d hI hD hd0 hgap hσ
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hu4 := hu.contDiffAt (hU.mem_nhds hyU)
  have he := modifiedSigma_eventuallyEq_complexFrame_general hU (hu.of_le (by norm_num)) a b hneg hyU Q hQ
  have hpos' : ∀ z ∈ U, (complexHessian a' b' u z).PosDef := by
    intro z hz
    exact (complexHessian_posDef_complexFrame_iff
      ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) Q hQ a b).mpr (hpos z hz)
  have hgp : ∀ j, j ≠ i → d j^2 < d i^2 := by
    intro j hj
    linarith [hgap j hj]
  have hj := modifiedSigma_normalized_jet hU hu a' b' hneg hpos' hyU i d hI hD hgp
  have hσ' : 0 ≤ modifiedSigma a' b' u y := by rw [he.eq_of_nhds]; exact hσ
  have hd1 : ∀ j, d j ≤ 1 := by
    have hi : d i ≤ 1 := by nlinarith [hj.2.1]
    intro j
    by_cases hji : j=i
    · simpa [hji] using hi
    · nlinarith [hgp j hji,hd0 i,hd0 j]
  have hb := modifiedSigma_normalized_fullQ_error_general hU hu a' b'
    (transformedDensity_ne_zero Q hQ hρ)
    (constantDensity_complexFrame hU (hu.of_le (by norm_num)) Q a b ρ hdet)
    hneg hpos' hyU i d hI hD hB hδ hd0 hgap hσ' (hy Q hQ d i hI hD hd0 hd1)
  have hs : ContDiffAt ℝ 2 (modifiedSigma a b u) y := hj.1.congr_of_eventuallyEq he.symm
  have hec : (fun z => (modifiedSigma a' b' u z : ℂ)) =ᶠ[𝓝 y]
      (fun z => (modifiedSigma a b u z : ℂ)) := he.mono (fun z hz => congrArg Complex.ofReal hz)
  have hc : (∑ p, ∑ q, (complexHessian a' b' u y)⁻¹ q p*
      dz (a' q) (-b' q) (dz (a' p) (b' p) (fun z => (modifiedSigma a' b' u z : ℂ))) y) =
      (∑ p, ∑ q, (complexHessian a b u y)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun z => (modifiedSigma a b u z : ℂ))) y) := by
    simp_rw [dz_dz_congr_nhds hec]
    exact complex_contraction_complexFrame (hu4.of_le (by norm_num)) hs Q hQ a b
  rw [hc,he.eq_of_nhds,he.fderiv_eq] at hb
  exact hb

end PowerConvexity
