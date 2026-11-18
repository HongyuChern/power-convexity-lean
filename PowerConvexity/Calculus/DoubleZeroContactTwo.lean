import PowerConvexity.Calculus.MatrixZeroContactTwo
import PowerConvexity.Calculus.ModifiedContactContractionTwo
import PowerConvexity.Calculus.NormalizedWeight
import PowerConvexity.Algebra.DimensionTwoStrictSign

/-! # The actual normalized double-zero contact

At A=I and B=I the Schur matrix vanishes. Neighbourhood semidefiniteness
forces every first derivative to vanish. The exact second contraction then
forces the skew third-derivative matrix to vanish. No propagation is claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem modifiedSchur_double_zero_matrix {u : E → ℝ} {x : E} (a b : Fin 2 → E)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ))) :
    modifiedSchur a b u x = 0 := by
  unfold modifiedSchur
  rw [hI,hD]
  have hh := matrixSchur_one_real_diagonal (fun _ : Fin 2 => (1:ℝ))
  simpa using hh

theorem modifiedSchur_double_zero_contraction_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ))) :
    matrixL a b u (modifiedSchur a b u) x 0 0 =
      (Complex.normSq (skewThirdHessian a b u 0 x).trace:ℂ)-
        ∑ p,∑ s,(Complex.normSq (skewThirdHessian a b u 0 x p s):ℂ) := by
  let W := skewThirdHessian a b u 0 x
  let G := (complexHessian a b u x)⁻¹
  let τ : ℂ := (powerWeight (u x):ℂ)*
    (complexGradient a b u x 0-star (complexGradient a b u x 0))
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu3 : ContDiffAt ℝ 3 u x := hu4.of_le (by norm_num)
  have hW : W.conjTranspose = -W := skewThirdHessian_conjTranspose hu3 a b 0
  have hG : G = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hpos x hx)
  have htr : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0 := by
    rw [← hG]
    exact skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  have hzero := modifiedSchur_double_zero_matrix a b hI hD
  have hdM (p : Fin 2) : matrixDZ (a p) (b p) (modifiedSchur a b u) x = 0 :=
    matrixDZ_eq_zero_of_posSemidef_zero_two
      (fun i j => (modifiedSchur_contDiffAt_two hu4 (hneg x hx) a b (hpos x hx) i j).of_le (by norm_num))
      hM hzero (a p) (b p)
  have hcomp (p s : Fin 2) : modifiedCompensatedHessian a b u p x 0 s =
      W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s := by
    have hh := modifiedSchur_dz_contact_row hu4 (hneg x hx) a b (hpos x hx)
      (fun _ => 1) hI hD 0 s p rfl
    have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 s) (hdM p)
    change dz (a p) (b p) (fun y => modifiedSchur a b u y 0 s) x = 0 at hz
    rw [hz] at hh
    simp only [Complex.ofReal_one,one_mul] at hh
    change 0 = W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s-
      modifiedCompensatedHessian a b u p x 0 s at hh
    linear_combination hh
  have hl := modifiedSchur_LM_contact_two hU hu a b hρ hdet hneg hpos hx
    (fun _ => 1) hI hD rfl
  change matrixL a b u (modifiedSchur a b u) x 0 0 =
    typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace-
      ∑ s,weightedSquare G (fun p => modifiedCompensatedHessian a b u p x 0 s) at hl
  simp_rw [hcomp] at hl
  rw [hG,typeI_rankOne_trace_zero_two W hW r htr,
    weightedSquare_column_shift_two _ W hW τ,htr,mul_zero,add_zero] at hl
  change matrixL a b u (modifiedSchur a b u) x 0 0 =
    (Complex.normSq W.trace:ℂ)-∑ p,∑ s,(Complex.normSq (W p s):ℂ)
  linear_combination hl

theorem skewThirdHessian_zero_at_double_zero_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ))) :
    skewThirdHessian a b u 0 x = 0 := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu3 : ContDiffAt ℝ 3 u x := hu4.of_le (by norm_num)
  have hn := matrixL_diagonal_re_nonneg_of_posSemidef_zero_two
    (modifiedSchur_contDiffAt_two hu4 (hneg x hx) a b (hpos x hx)) hM
    (modifiedSchur_double_zero_matrix a b hI hD) a b (hpos x hx) 0
  rw [modifiedSchur_double_zero_contraction_two hU hu a b hρ hdet hneg hpos hx hM hI hD] at hn
  simp only [Complex.sub_re,Complex.re_sum,Complex.ofReal_re] at hn
  by_contra hne
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hG : (complexHessian a b u x)⁻¹ = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hpos x hx)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  rw [hG] at ht
  have hs := dimensionTwo_skew_strict_sign _ (skewThirdHessian_conjTranspose hu3 a b 0) r ht hne
  linarith

end PowerConvexity
