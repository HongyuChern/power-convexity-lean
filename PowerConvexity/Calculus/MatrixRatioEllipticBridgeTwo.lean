import PowerConvexity.Calculus.QuotientRatioEllipticEstimateTwo
import PowerConvexity.Calculus.HermitianDerivativeNormsTwo

/-! # Applying the scalar ratio estimate to actual Hermitian matrix fields -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def matrixRatioZeroCoefficientTwo (K B0 B1 ell Λ : ℝ) : ℝ :=
  (4*B0+Λ*(2*K+22*K^2))+4*K*(4*B1+8*Λ*K)+5*(4*B1+8*Λ*K)^2/ell

noncomputable def matrixRatioGradientCoefficientTwo (K B1 Λ : ℝ) : ℝ :=
  2*(4*B1+8*Λ*K)

theorem matrixRatioZeroCoefficientTwo_nonneg {K B0 B1 ell Λ : ℝ}
    (hK : 0 ≤ K) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    0 ≤ matrixRatioZeroCoefficientTwo K B0 B1 ell Λ := by
  unfold matrixRatioZeroCoefficientTwo
  positivity

theorem matrixRatioGradientCoefficientTwo_nonneg {K B1 Λ : ℝ}
    (hK : 0 ≤ K) (hB1 : 0 ≤ B1) (hΛ : 0 ≤ Λ) :
    0 ≤ matrixRatioGradientCoefficientTwo K B1 Λ := by
  unfold matrixRatioGradientCoefficientTwo
  positivity

theorem matrixQuotientRatioTwo_elliptic_estimate
    {M A : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun y => A y i j) x)
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian ∧ (A y).IsHermitian)
    (hI : A x = 1) (s : Fin 2 → ℝ)
    (hD : M x = Matrix.diagonal (fun i => (s i:ℂ)))
    (hs : ∀ i, 0 ≤ s i) (ht : 0 < s 0+s 1)
    {K B0 B1 ell Λ : ℝ} (hK : 0 ≤ K) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hjets : ∀ i j,
      ‖fderiv ℝ (fun y => (A y i j).re) x‖ ≤ K ∧
      ‖fderiv ℝ (fun y => (A y i j).im) x‖ ≤ K ∧
      ‖realHessian (fun y => (A y i j).re) x‖ ≤ K)
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    (hlow : ∀ v : E, ell*‖v‖^2 ≤ L (realRankOneForm v))
    (htrace : L (realInnerForm (E := E)) ≤ Λ)
    (hdiag : ∀ k, L (realHessian (fun y => (M y k k).re) x) ≤
      B0*(s 0+s 1)+B1*hermitianDerivativeSumTwo M x) :
    L (realHessian (matrixQuotientRatioTwo M A) x) ≤
      matrixRatioZeroCoefficientTwo K B0 B1 ell Λ*(s 0+s 1)+
      matrixRatioGradientCoefficientTwo K B1 Λ*‖fderiv ℝ (matrixQuotientRatioTwo M A) x‖ := by
  have hMr (i j : Fin 2) : ContDiffAt ℝ 2 (fun y => (M y i j).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hM i j)
  have hMi (i j : Fin 2) : ContDiffAt ℝ 2 (fun y => (M y i j).im) x :=
    Complex.imCLM.contDiff.contDiffAt.comp x (hM i j)
  have hAr (i j : Fin 2) : ContDiffAt ℝ 2 (fun y => (A y i j).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hA i j)
  have hAi (i j : Fin 2) : ContDiffAt ℝ 2 (fun y => (A y i j).im) x :=
    Complex.imCLM.contDiff.contDiffAt.comp x (hA i j)
  have hh := hermitianQuotientRatioFieldTwo_elliptic_estimate
    (hMr 0 0) (hMr 1 1) (hMr 0 1) (hMi 0 1)
    (hAr 0 0) (hAr 1 1) (hAr 0 1) (hAi 0 1)
    (by simp [hD]) (by simp [hD]) (by simp [hI]) (by simp [hI])
    (by simp [hI]) (by simp [hI])
    (by simpa [hD] using hs 0) (by simpa [hD] using hs 1)
    (by simpa [hD] using ht) hK hB0 hB1 hell hΛ
    (hjets 0 0).1 (hjets 1 1).1 (hjets 0 1).1 (hjets 0 1).2.1
    (hjets 0 0).2.2 (hjets 1 1).2.2 L hL hlow htrace
    (by simpa [hD,hermitianDerivativeSumTwo] using hdiag 0)
    (by simpa [hD,hermitianDerivativeSumTwo] using hdiag 1)
  have hH := matrixQuotientRatioTwo_realHessian_normalized_bridge
    (fun i j => (hM i j).continuousAt) (fun i j => (hA i j).continuousAt) hherm hI s hD ht.ne'
  have hF := matrixQuotientRatioTwo_fderiv_normalized_bridge
    (fun i j => (hM i j).continuousAt) (fun i j => (hA i j).continuousAt) hherm hI s hD ht.ne'
  rw [hH,hF]
  simpa only [matrixQuotientRatioRealFieldTwo,matrixRatioZeroCoefficientTwo,
    matrixRatioGradientCoefficientTwo,hD,Matrix.diagonal_apply_eq,Complex.ofReal_re,
    Function.comp_def,Complex.reCLM_apply,Complex.imCLM_apply] using hh

end PowerConvexity
