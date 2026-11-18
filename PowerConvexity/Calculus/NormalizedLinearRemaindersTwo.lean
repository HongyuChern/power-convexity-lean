import PowerConvexity.Calculus.NormalizedSpectralJetBoundsTwo

/-! # Actual sigma LA and Dsigma DA errors with the Frechet gradient norm -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_linear_remainders_bounds {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) {B : ℝ} (hB : 0 ≤ B)
    (hjets : normalizedSpectralJetBoundTwo a b u x B) :
    ‖(modifiedSigmaTwo a b u x:ℂ)*matrixL a b u (modifiedA a b u) x 0 0‖ ≤
      4*B^2*modifiedSigmaTwo a b u x ∧
    ‖spectralGradientCrossTwo (complexHessian a b u x)⁻¹
      (fun p => dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ)) x)
      (fun p => dz (a p) (b p) (fun y => modifiedA a b u y 0 0) x)‖ ≤
      8*B^3*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
  obtain ⟨hbase,_,_,_,_,hAb,_,hAsecond,hdir⟩ := hjets
  obtain ⟨_,hgap,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have hs := (modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) hgap).differentiableAt (by norm_num)
  have hsn : ‖(modifiedSigmaTwo a b u x:ℂ)‖ = modifiedSigmaTwo a b u x := by
    simp [Complex.norm_real,abs_of_nonneg hσ0]
  have hL : ‖matrixL a b u (modifiedA a b u) x 0 0‖ ≤ 4*B^2 := by
    rw [matrixL_entry]
    convert doubleContraction_norm_le_two _ _ hB hbase.1 hAsecond using 1 <;> ring
  have hsg (p : Fin 2) : ‖dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ)) x‖ ≤
      B*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
    refine (norm_dz_ofReal_le hs (a p) (b p)).trans ?_
    exact mul_le_mul_of_nonneg_right (hdir p) (norm_nonneg _)
  constructor
  · rw [norm_mul,hsn]
    calc
      _ ≤ modifiedSigmaTwo a b u x*(4*B^2) := mul_le_mul_of_nonneg_left hL hσ0
      _ = _ := by ring
  · convert spectralGradientCrossTwo_norm_le _ _ _ hB
      (by positivity : 0 ≤ B*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖)
      hbase.1 hsg (fun p => hAb p 0 0) using 1 <;> ring

end PowerConvexity
