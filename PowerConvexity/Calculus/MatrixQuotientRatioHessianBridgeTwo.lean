import PowerConvexity.Algebra.HermitianQuotientCoordinatesTwo
import PowerConvexity.Calculus.HermitianQuotientRatioHessianTwo

/-! # Actual matrix inverse quotient to the scalar Hessian formula

Hermitian structure is required on a neighborhood, while normalization is only
at the point. No differentiable diagonalizing frame is introduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def matrixQuotientRatioTwo (M A : E → Matrix (Fin 2) (Fin 2) ℂ) (x : E) : ℝ :=
  traceDetRatioTwo (M x*(A x)⁻¹).trace.re (M x*(A x)⁻¹).det.re
noncomputable def matrixQuotientRatioRealFieldTwo (M A : E → Matrix (Fin 2) (Fin 2) ℂ) : E → ℝ :=
  hermitianQuotientRatioFieldTwo
    (fun y => (M y 0 0).re) (fun y => (M y 1 1).re)
    (fun y => (M y 0 1).re) (fun y => (M y 0 1).im)
    (fun y => (A y 0 0).re) (fun y => (A y 1 1).re)
    (fun y => (A y 0 1).re) (fun y => (A y 0 1).im)

theorem matrixQuotientRatioTwo_eventually_eq_realField
    {M A : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContinuousAt (fun y => M y i j) x)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian ∧ (A y).IsHermitian)
    (hDelta : (A x 0 0).re*(A x 1 1).re-(A x 0 1).re^2-(A x 0 1).im^2 ≠ 0)
    (hT : (M x 0 0).re*(A x 1 1).re+(M x 1 1).re*(A x 0 0).re-
      2*((M x 0 1).re*(A x 0 1).re+(M x 0 1).im*(A x 0 1).im) ≠ 0) :
    matrixQuotientRatioTwo M A =ᶠ[𝓝 x] matrixQuotientRatioRealFieldTwo M A := by
  have hAr (i j : Fin 2) : ContinuousAt (fun y => (A y i j).re) x :=
    Complex.continuous_re.continuousAt.comp (hA i j)
  have hAi (i j : Fin 2) : ContinuousAt (fun y => (A y i j).im) x :=
    Complex.continuous_im.continuousAt.comp (hA i j)
  have hMr (i j : Fin 2) : ContinuousAt (fun y => (M y i j).re) x :=
    Complex.continuous_re.continuousAt.comp (hM i j)
  have hMi (i j : Fin 2) : ContinuousAt (fun y => (M y i j).im) x :=
    Complex.continuous_im.continuousAt.comp (hM i j)
  have hDeltaC : ContinuousAt (fun y => (A y 0 0).re*(A y 1 1).re-
      (A y 0 1).re^2-(A y 0 1).im^2) x :=
    (((hAr 0 0).mul (hAr 1 1)).sub ((hAr 0 1).pow 2)).sub ((hAi 0 1).pow 2)
  have hTC : ContinuousAt (fun y => (M y 0 0).re*(A y 1 1).re+
      (M y 1 1).re*(A y 0 0).re-
      2*((M y 0 1).re*(A y 0 1).re+(M y 0 1).im*(A y 0 1).im)) x :=
    (((hMr 0 0).mul (hAr 1 1)).add ((hMr 1 1).mul (hAr 0 0))).sub
      (continuousAt_const.mul (((hMr 0 1).mul (hAr 0 1)).add ((hMi 0 1).mul (hAi 0 1))))
  filter_upwards [hherm,hDeltaC.eventually_ne hDelta,hTC.eventually_ne hT] with y hy hdy hty
  have hMM := hermitianMatrixTwo_eq_of_isHermitian (M y) hy.1
  have hAA := hermitianMatrixTwo_eq_of_isHermitian (A y) hy.2
  unfold matrixQuotientRatioTwo
  rw [hMM,hAA]
  have hh := hermitianMatrixTwo_quotient_ratio
    (M y 0 0).re (M y 1 1).re (M y 0 1).re (M y 0 1).im
    (A y 0 0).re (A y 1 1).re (A y 0 1).re (A y 0 1).im hdy hty
  simpa only [matrixQuotientRatioRealFieldTwo,hermitianQuotientRatioFieldTwo,
    hermitianAdjTraceFieldTwo,hermitianDetFieldTwo,pow_two] using hh

theorem matrixQuotientRatioTwo_realHessian_normalized_bridge
    {M A : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContinuousAt (fun y => M y i j) x)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian ∧ (A y).IsHermitian)
    (hI : A x = 1) (d : Fin 2 → ℝ)
    (hD : M x = Matrix.diagonal (fun i => (d i:ℂ))) (ht : d 0+d 1 ≠ 0) :
    realHessian (matrixQuotientRatioTwo M A) x =
      realHessian (matrixQuotientRatioRealFieldTwo M A) x := by
  have hnear := matrixQuotientRatioTwo_eventually_eq_realField hM hA hherm
    (by simp [hI]) (by simpa [hI,hD] using ht)
  exact hnear.fderiv.fderiv_eq

theorem matrixQuotientRatioTwo_fderiv_normalized_bridge
    {M A : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContinuousAt (fun y => M y i j) x)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian ∧ (A y).IsHermitian)
    (hI : A x = 1) (d : Fin 2 → ℝ)
    (hD : M x = Matrix.diagonal (fun i => (d i:ℂ))) (ht : d 0+d 1 ≠ 0) :
    fderiv ℝ (matrixQuotientRatioTwo M A) x =
      fderiv ℝ (matrixQuotientRatioRealFieldTwo M A) x := by
  have hnear := matrixQuotientRatioTwo_eventually_eq_realField hM hA hherm
    (by simp [hI]) (by simpa [hI,hD] using ht)
  exact hnear.fderiv_eq

end PowerConvexity
