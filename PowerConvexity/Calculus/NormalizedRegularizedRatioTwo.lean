import PowerConvexity.Calculus.MatrixRatioEllipticBridgeTwo
import PowerConvexity.Calculus.SchurRealDiagonalBoundsTwo
import PowerConvexity.Calculus.RegularizedDiagonalEstimates
import PowerConvexity.Calculus.ActualSchurRatioRegularizationTwo

/-! # The actual regularized Schur ratio in one fixed normalized frame

All matrix derivatives below belong to M + epsilon A. The constants are
explicit and do not contain epsilon or the difference of the two eigenvalues.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem regularizedModifiedSchurTwo_entry_re (a b : Fin 2 → E) (u : E → ℝ)
    (ε : ℝ) (x : E) (i j : Fin 2) :
    (regularizedModifiedSchurTwo a b u ε x i j).re =
      (modifiedSchur a b u x i j).re+ε*(modifiedA a b u x i j).re := by
  simp [regularizedModifiedSchurTwo,Complex.mul_re]

theorem regularizedModifiedSchurTwo_entry_im (a b : Fin 2 → E) (u : E → ℝ)
    (ε : ℝ) (x : E) (i j : Fin 2) :
    (regularizedModifiedSchurTwo a b u ε x i j).im =
      (modifiedSchur a b u x i j).im+ε*(modifiedA a b u x i j).im := by
  simp [regularizedModifiedSchurTwo,Complex.mul_im]

theorem regularizedModifiedSchurTwo_normalized_diagonal
    (a b : Fin 2 → E) (u : E → ℝ) (ε : ℝ) (x : E) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ))) :
    regularizedModifiedSchurTwo a b u ε x =
      Matrix.diagonal (fun i => ((1-(d i)^2+ε:ℝ):ℂ)) := by
  unfold regularizedModifiedSchurTwo modifiedSchur
  rw [hI,hD,matrixSchur_one_real_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem regularizedModifiedSchurTwo_hermitian
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (a b : Fin 2 → E) (hpos : (complexHessian a b u x).PosDef) (ε : ℝ) :
    (regularizedModifiedSchurTwo a b u ε x).IsHermitian := by
  exact (modifiedSchur_isHermitian hu hx a b hpos).add
    ((modifiedA_posDef a b hx hpos).isHermitian.smul (by simp [IsSelfAdjoint]))

theorem regularizedModifiedSchurTwo_gradient_sum_bound
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0)
    (a b : Fin 2 → E) (hpos : (complexHessian a b u x).PosDef)
    {ε K : ℝ} (hε : 0 ≤ ε)
    (hjets : ∀ i j,
      ‖fderiv ℝ (fun y => (modifiedA a b u y i j).re) x‖ ≤ K ∧
      ‖fderiv ℝ (fun y => (modifiedA a b u y i j).im) x‖ ≤ K) :
    hermitianDerivativeSumTwo (modifiedSchur a b u) x ≤
      hermitianDerivativeSumTwo (regularizedModifiedSchurTwo a b u ε) x+4*ε*K := by
  have hM := modifiedSchur_contDiffAt_two hu hx a b hpos
  have hA := modifiedA_contDiffAt_two hu hx a b
  have hMr (i j : Fin 2) : DifferentiableAt ℝ (fun y => (modifiedSchur a b u y i j).re) x :=
    Complex.reCLM.differentiableAt.comp x ((hM i j).differentiableAt (by norm_num))
  have hMi (i j : Fin 2) : DifferentiableAt ℝ (fun y => (modifiedSchur a b u y i j).im) x :=
    Complex.imCLM.differentiableAt.comp x ((hM i j).differentiableAt (by norm_num))
  have hAr (i j : Fin 2) : DifferentiableAt ℝ (fun y => (modifiedA a b u y i j).re) x :=
    Complex.reCLM.differentiableAt.comp x ((hA i j).differentiableAt (by norm_num))
  have hAi (i j : Fin 2) : DifferentiableAt ℝ (fun y => (modifiedA a b u y i j).im) x :=
    Complex.imCLM.differentiableAt.comp x ((hA i j).differentiableAt (by norm_num))
  have hh := four_gradient_norms_le_regularized
    (hMr 0 0) (hMr 1 1) (hMr 0 1) (hMi 0 1)
    (hAr 0 0) (hAr 1 1) (hAr 0 1) (hAi 0 1) hε
    (hjets 0 0).1 (hjets 1 1).1 (hjets 0 1).1 (hjets 0 1).2
  simpa only [hermitianDerivativeSumTwo,regularizedModifiedSchurTwo_entry_re,
    regularizedModifiedSchurTwo_entry_im] using hh

noncomputable def regularizedSchurDiagonalCoefficientTwo (B K Λ : ℝ) : ℝ :=
  (768*B^5+96*B^3)+2*(48*B^3)*K+(K*Λ)/2

noncomputable def regularizedSchurRatioCoefficientTwo (B K ell Λ : ℝ) : ℝ :=
  matrixRatioZeroCoefficientTwo K (regularizedSchurDiagonalCoefficientTwo B K Λ) (48*B^3) ell Λ+
    matrixRatioGradientCoefficientTwo K (48*B^3) Λ

theorem regularizedSchurRatioCoefficientTwo_nonneg {B K ell Λ : ℝ}
    (hB : 1 ≤ B) (hK : 0 ≤ K) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    0 ≤ regularizedSchurRatioCoefficientTwo B K ell Λ := by
  have hB0 : 0 ≤ B := by linarith
  apply add_nonneg
  · apply matrixRatioZeroCoefficientTwo_nonneg hK _ (by positivity) hell hΛ
    unfold regularizedSchurDiagonalCoefficientTwo
    positivity
  · exact matrixRatioGradientCoefficientTwo_nonneg hK (by positivity) hΛ

variable [CompleteSpace E]

theorem modifiedTraceRatioRegularizedTwo_normalized_estimate
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : Fin 2 → E) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hM : (modifiedSchur a b u x).PosSemidef)
    {B K ell Λ : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K) (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hdir : ∀ p, (‖a p‖+‖b p‖)/2 ≤ B)
    (hjets : ∀ k, normalizedSpectralJetBoundTwo
      (a ∘ Equiv.swap (0:Fin 2) k) (b ∘ Equiv.swap (0:Fin 2) k) u x B)
    (hAjets : ∀ i j,
      ‖fderiv ℝ (fun y => (modifiedA a b u y i j).re) x‖ ≤ K ∧
      ‖fderiv ℝ (fun y => (modifiedA a b u y i j).im) x‖ ≤ K ∧
      ‖realHessian (fun y => (modifiedA a b u y i j).re) x‖ ≤ K ∧
      complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realHessian (fun y => (modifiedA a b u y i j).re) x) ≤ K*Λ)
    (hlow : ∀ v : E, ell*‖v‖^2 ≤
      complexHessianContraction a b (complexHessian a b u x)⁻¹ (realRankOneForm v))
    (htrace : complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realInnerForm (E := E)) ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    complexLinearized a b u (modifiedTraceRatioRegularizedTwo a b u ε) x ≤
      regularizedSchurRatioCoefficientTwo B K ell Λ*
        (modifiedTraceRatioRegularizedTwo a b u ε x+
          ‖fderiv ℝ (modifiedTraceRatioRegularizedTwo a b u ε) x‖) := by
  let L := complexHessianContraction a b (complexHessian a b u x)⁻¹
  let M := modifiedSchur a b u
  let A := modifiedA a b u
  let R := regularizedModifiedSchurTwo a b u ε
  let s : Fin 2 → ℝ := fun i => 1-(d i)^2+ε
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu2 : ContDiffAt ℝ 2 u x := hu4.of_le (by norm_num)
  have hMR := modifiedSchur_contDiffAt_two hu4 (hneg x hx) a b (hpos x hx)
  have hAR := modifiedA_contDiffAt_two hu4 (hneg x hx) a b
  have hRR := regularizedModifiedSchurTwo_contDiffAt_two hu4 (hneg x hx) a b (hpos x hx) ε
  have hdSq (i : Fin 2) : 0 ≤ 1-(d i)^2 := by nlinarith [(hd i).1,(hd i).2]
  have hs (i : Fin 2) : 0 ≤ s i := by dsimp only [s]; linarith [hdSq i]
  have ht : 0 < s 0+s 1 := by dsimp only [s]; linarith [hdSq 0,hdSq 1]
  have htold : 2-(d 0)^2-(d 1)^2 ≤ s 0+s 1 := by dsimp only [s]; linarith
  have heT : 2*ε ≤ s 0+s 1 := by dsimp only [s]; linarith [hdSq 0,hdSq 1]
  have hRdiag : R x = Matrix.diagonal (fun i => (s i:ℂ)) :=
    regularizedModifiedSchurTwo_normalized_diagonal a b u ε x d hI hD
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ regularizedSchurDiagonalCoefficientTwo B K Λ := by
    unfold regularizedSchurDiagonalCoefficientTwo
    positivity
  have hsum := regularizedModifiedSchurTwo_gradient_sum_bound hu4 (hneg x hx) a b
    (hpos x hx) hε.le (fun i j => ⟨(hAjets i j).1,(hAjets i j).2.1⟩)
  have hdiag (k : Fin 2) : L (realHessian (fun y => (R y k k).re) x) ≤
      regularizedSchurDiagonalCoefficientTwo B K Λ*(s 0+s 1)+
        (48*B^3)*hermitianDerivativeSumTwo R x := by
    have hMr : ContDiffAt ℝ 2 (fun y => (M y k k).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp x (hMR k k)
    have hAr : ContDiffAt ℝ 2 (fun y => (A y k k).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp x (hAR k k)
    have hh := regularized_diagonal_contraction_bound hMr hAr L hε.le htold heT hK
      (by positivity : 0 ≤ 768*B^5+96*B^3) (by positivity : 0 ≤ 48*B^3)
      (by positivity : 0 ≤ K*Λ) hsum
      (modifiedSchur_real_diagonal_trace_bound_two hU hu a b hρ hdet hneg hpos hx d hI hD hd
        hB hdir k (hjets k)) (hAjets k k).2.2.2
    simpa only [R,M,A,regularizedModifiedSchurTwo_entry_re,
      regularizedSchurDiagonalCoefficientTwo] using hh
  have hherm : ∀ᶠ y in 𝓝 x, (R y).IsHermitian ∧ (A y).IsHermitian := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨regularizedModifiedSchurTwo_hermitian
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) (hneg y hy) a b (hpos y hy) ε,
      (modifiedA_posDef a b (hneg y hy) (hpos y hy)).isHermitian⟩
  have hh := matrixQuotientRatioTwo_elliptic_estimate hRR hAR hherm hI s hRdiag hs ht
    hK hC0 (by positivity : 0 ≤ 48*B^3) hell hΛ
    (fun i j => ⟨(hAjets i j).1,(hAjets i j).2.1,(hAjets i j).2.2.1⟩)
    L (complexHessianContraction_positive a b (hpos x hx).inv) hlow htrace hdiag
  have hFH := modifiedTraceRatioRegularizedTwo_realHessian_eq_matrixQuotient a b ε hU hneg hpos hx
  have hFD := modifiedTraceRatioRegularizedTwo_fderiv_eq_matrixQuotient a b ε hU hneg hpos hx
  have hFval := modifiedTraceRatioRegularizedTwo_eq_matrixQuotient a b u ε (hneg x hx) (hpos x hx)
  have hFge : s 0+s 1 ≤ modifiedTraceRatioRegularizedTwo a b u ε x := by
    rw [hFval]
    change s 0+s 1 ≤ matrixQuotientRatioTwo R A x
    unfold matrixQuotientRatioTwo
    rw [show A x = 1 from hI,inv_one,Matrix.mul_one,hRdiag]
    simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Matrix.diagonal_apply_eq,
      Complex.add_re,Complex.ofReal_re,Matrix.det_fin_two,Matrix.diagonal_apply_ne _ (by decide : (0:Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1:Fin 2) ≠ 0),zero_mul,sub_zero]
    have hq : 0 ≤ ((s 0:ℂ)*(s 1:ℂ)).re/(s 0+s 1) := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact div_nonneg (mul_nonneg (hs 0) (hs 1)) ht.le
    exact le_add_of_nonneg_right hq
  rw [complexLinearized_eq_real a b u
    (modifiedTraceRatioRegularizedTwo_contDiffAt hu4 (hneg x hx) a b (hpos x hx) hM hε)]
  have hCz := matrixRatioZeroCoefficientTwo_nonneg hK hC0
    (by positivity : 0 ≤ 48*B^3) hell hΛ
  have hCg := matrixRatioGradientCoefficientTwo_nonneg hK (by positivity : 0 ≤ 48*B^3) hΛ
  change L (realHessian (modifiedTraceRatioRegularizedTwo a b u ε) x) ≤ _
  change L (realHessian (matrixQuotientRatioTwo R A) x) ≤ _ at hh
  rw [← hFH,← hFD] at hh
  have h1 := mul_le_mul_of_nonneg_left hFge hCz
  have hF0 : 0 ≤ modifiedTraceRatioRegularizedTwo a b u ε x := ht.le.trans hFge
  have h2 := mul_nonneg hCg hF0
  have h3 := mul_nonneg hCz (norm_nonneg (fderiv ℝ (modifiedTraceRatioRegularizedTwo a b u ε) x))
  unfold regularizedSchurRatioCoefficientTwo
  nlinarith only [hh,h1,h2,h3]

end PowerConvexity
