import PowerConvexity.Calculus.NormalizedSpectralJetBoundsTwo
import PowerConvexity.Calculus.NormalizedWeight
import PowerConvexity.Algebra.QuadraticDefectEstimateTwo

/-! # The actual completed quadratic form away from critical zero contact -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_leadingQuadratic_bound {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) {B : ℝ} (hB : 0 ≤ B)
    (hjets : normalizedSpectralJetBoundTwo a b u x B) :
    (contactFullQuadraticTwo (complexHessian a b u x)⁻¹ (skewThirdHessian a b u 0 x)
      (fun p s => modifiedCompensatedHessian a b u p x 0 s)
      ((powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))) (d 1)).re ≤
      72*B^3*modifiedSigmaTwo a b u x+24*B^3*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
  obtain ⟨hbase,hW,hDb,hτ,hR,hAb,_,_,hdir⟩ := hjets
  obtain ⟨hσ,_,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have ht1 : d 0 ≤ 1 := by nlinarith
  have hb1 : d 1 < 1 := ho.trans_le ht1
  have hμ : 0 < 1-(d 1)^2 := by nlinarith
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun p s => modifiedCompensatedHessian a b u p x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hG : (complexHessian a b u x)⁻¹ = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hA x hx)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  rw [hG] at ht
  have hGb : ∀ p q, ‖rankOneWeightTwo r q p‖ ≤ B := by
    intro p q
    rw [← hG]
    exact hbase.1 q p
  have hX : ∀ p, ‖W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0‖ ≤ 3*B := by
    intro p
    exact (contactShiftedColumn_entry_bound_two hB W τ hW hτ p 0).trans (by linarith)
  have hDb' : ∀ p, ‖D p 0‖ ≤ 3*B := by intro p; exact (hDb p 0).trans (by linarith)
  have hdef : ∀ p, ‖D p 0-(W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0)‖ ≤
      3*B*modifiedSigmaTwo a b u x+B*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
    intro p
    refine (modifiedCompensated_first_column_defect_norm hU hu a b hneg hA hx d hI hD
      hd0 hd1 ho hσ0 p hB (hDb p 0) (hR p 0) (hAb p 0 0)).trans ?_
    gcongr
    exact hdir p
  have he := contactFullQuadraticTwo_le_defect_norm W D (skewThirdHessian_conjTranspose hu3 a b 0)
    r τ (d 1) hμ ht hB (by positivity : 0 ≤ 3*B)
    (by positivity : 0 ≤ 3*B*modifiedSigmaTwo a b u x+B*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖)
    hGb hX hDb' hdef
  rw [hG]
  convert he using 1 <;> ring

end PowerConvexity
