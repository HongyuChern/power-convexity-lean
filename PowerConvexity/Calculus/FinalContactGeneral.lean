import PowerConvexity.Calculus.ModifiedContactSpectrumGeneral
import PowerConvexity.Calculus.ModifiedContactContractionGeneral
import PowerConvexity.Calculus.NormalizedWeight
import PowerConvexity.Algebra.WeightedSpectralContraction

/-! # Actual arbitrary-dimensional final_fullQ on the zero critical locus

Every tensor below is the actual derivative of the same C4 potential. The
pointwise identity has no dimension-two sign premise and gives no such sign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedSigma_contact_contraction_eq_quadratic {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hd : d i = 1) (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hc : fderiv ℝ (modifiedSigma a b u) x = 0) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x) =
    contactFullQuadratic (complexHessian a b u x)⁻¹ (skewThirdHessian a b u i x)
      (fun p s => modifiedCompensatedHessian a b u p x i s)
      ((powerWeight (u x) : ℂ) * (complexGradient a b u x i - star (complexGradient a b u x i))) d i := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u i x
  let D : Matrix ι ι ℂ := fun p s => modifiedCompensatedHessian a b u p x i s
  let τ : ℂ := (powerWeight (u x) : ℂ) * (complexGradient a b u x i - star (complexGradient a b u x i))
  have hrow (s p : ι) : dz (a p) (b p) (fun y => modifiedSchur a b u y i s) x =
      contactUpperVector W D τ d s p :=
    modifiedSchur_dz_contact_row (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD i s p hd
  have hcol (s p : ι) : dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x =
      contactLowerVector W D τ d s p :=
    modifiedSchur_dz_contact_column (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD i s p hd
  have hmix (p q : ι) := modifiedSigma_contact_mixed hU hu a b hneg hA hx i d hI hD hd hgap hc p q
  have hl := modifiedSchur_LM_contact_general hU hu a b hρ hdet hneg hA hx d i hI hD hd
  simp only [matrixL, contract, Matrix.sum_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul, matrixDZ] at hl
  change (∑ p, ∑ q, G q p *
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedSchur a b u y i i)) x) =
    typeIQuadratic G W + (Complex.normSq τ : ℂ) * G.trace -
      ∑ s, weightedSquare G (fun p => D p s) at hl
  change (∑ p, ∑ q, G q p *
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x) =
    contactFullQuadratic G W D τ d i
  simp_rw [hmix, hrow, hcol]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [weightedSpectralContraction G
    (fun j : {j : ι // j ≠ i} => contactUpperVector W D τ d j)
    (fun j : {j : ι // j ≠ i} => contactLowerVector W D τ d j)
    (fun j => 1 - (d j : ℂ)^2)]
  rw [sum_complement_eq_erase (fun s : ι =>
    (weightedSquare G (contactUpperVector W D τ d s) +
      weightedSquare G (contactLowerVector W D τ d s)) / (1 - (d s : ℂ)^2)) i]
  simp only [add_div, Finset.sum_add_distrib]
  rw [hl]
  unfold contactFullQuadratic contactQuadratic
  ring

/-- Frozen final_fullQ: exact at sigma = Dsigma = 0, in every finite dimension. -/
theorem modifiedSigma_final_fullQ_contact {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hd : d i = 1) (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hc : fderiv ℝ (modifiedSigma a b u) x = 0) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x) =
      (Complex.normSq (skewThirdHessian a b u i x).trace : ℂ) -
      (∑ p, ∑ s, (Complex.normSq (skewThirdHessian a b u i x p s) : ℂ)) -
      2 * ∑ s ∈ Finset.univ.erase i,
        weightedSquare (complexHessian a b u x)⁻¹
          (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x) /
          (1 - (d s : ℂ)^2) := by
  let W := skewThirdHessian a b u i x
  let D : Matrix ι ι ℂ := fun p s => modifiedCompensatedHessian a b u p x i s
  let τ : ℂ := (powerWeight (u x) : ℂ) * (complexGradient a b u x i - star (complexGradient a b u x i))
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hG : (complexHessian a b u x)⁻¹ = rankOneWeight r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hA x hx)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) i
  rw [hG] at ht
  have hμ (s : ι) (hs : s ≠ i) : 1 - (d s : ℂ)^2 ≠ 0 := by
    have hp : 0 < 1 - d s^2 := sub_pos.mpr (by simpa [hd] using hgap s hs)
    exact_mod_cast ne_of_gt hp
  have hDi : ∀ p, D p i = W p i + τ * (1 : Matrix ι ι ℂ) p i :=
    modifiedCompensated_contact_first_column_general hU hu a b hneg hA hx i d hI hD hd hgap hc
  have hcol (s : ι) : contactLowerVector W D τ d s =
      (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x) := by
    funext p
    exact (modifiedSchur_dz_contact_column (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
      (hA x hx) d hI hD i s p hd).symm
  rw [modifiedSigma_contact_contraction_eq_quadratic hU hu a b hρ hdet hneg hA hx i d hI hD hd hgap hc, hG]
  exact (contactFullQuadratic_eq W D (skewThirdHessian_conjTranspose hu3 a b i) r τ d i hμ ht hDi).trans
    (by simp_rw [hcol]; rfl)

end PowerConvexity
