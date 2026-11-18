import PowerConvexity.Calculus.ModifiedPencilGeneral

/-! # Actual simple-root derivatives at an arbitrary-dimensional zero contact -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedSchur_dzbar_eq_star_swap_general {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (i j q : ι) :
    dz (a q) (-b q) (fun y => modifiedSchur a b u y i j) x =
      star (dz (a q) (b q) (fun y => modifiedSchur a b u y j i) x) := by
  have he : (fun y => (modifiedSchur a b u y).conjTranspose) =ᶠ[𝓝 x] modifiedSchur a b u := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact modifiedSchur_isHermitian ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hA y hy)
  have hm : matrixDZ (a q) (-b q) (modifiedSchur a b u) x =
      (matrixDZ (a q) (b q) (modifiedSchur a b u) x).conjTranspose := by
    rw [← matrixDZ_conjTranspose]
    exact (matrixDZ_congr_nhds (a q) (-b q) he).symm
  exact congrArg (fun M : Matrix ι ι ℂ => M i j) hm

variable [CompleteSpace E]

theorem modifiedSigma_contact_dzMii {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hd : d i = 1) (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hc : fderiv ℝ (modifiedSigma a b u) x = 0) (v w : E) :
    dz v w (fun y => modifiedSchur a b u y i i) x = 0 := by
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hz : modifiedSigma a b u x = 0 := by simpa [hd] using hj.2.1
  have he := (modifiedSigma_dz_mixed_normalized_exact hU hu a b hneg hA hx i d hI hD hgap v w v w).1
  rw [dz_ofReal_eq_zero_of_fderiv_eq_zero (hj.1.differentiableAt (by norm_num)) hc, hz] at he
  simpa using he.symm

theorem modifiedSigma_contact_mixed {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hd : d i = 1) (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hc : fderiv ℝ (modifiedSigma a b u) x = 0) (p q : ι) :
    dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x =
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedSchur a b u y i i)) x -
      ∑ j : {j : ι // j ≠ i},
        (dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x *
          star (dz (a q) (b q) (fun y => modifiedSchur a b u y i j) x) +
         dz (a p) (b p) (fun y => modifiedSchur a b u y j i) x *
          star (dz (a q) (b q) (fun y => modifiedSchur a b u y j i) x)) /
          (1 - (d j : ℂ)^2) := by
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hz : modifiedSigma a b u x = 0 := by simpa [hd] using hj.2.1
  have he := (modifiedSigma_dz_mixed_normalized_exact hU hu a b hneg hA hx i d hI hD hgap
    (a p) (b p) (a q) (-b q)).2
  simp only [dz_ofReal_eq_zero_of_fderiv_eq_zero (hj.1.differentiableAt (by norm_num)) hc,
    hz, Complex.ofReal_zero, zero_mul, sub_zero, hd, one_pow, sub_self, zero_sub,
    div_neg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at he
  simp_rw [modifiedSchur_dzbar_eq_star_swap_general hU hu a b hneg hA hx] at he
  rw [Finset.sum_neg_distrib] at he
  rw [sub_eq_add_neg]
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem modifiedCompensated_contact_first_column_general {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hd : d i = 1) (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hc : fderiv ℝ (modifiedSigma a b u) x = 0) (p : ι) :
    modifiedCompensatedHessian a b u p x i i = skewThirdHessian a b u i x p i +
      (powerWeight (u x) : ℂ) * (complexGradient a b u x i - star (complexGradient a b u x i)) *
        (1 : Matrix ι ι ℂ) p i := by
  have hr := modifiedSchur_dz_contact_row (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
    (hA x hx) d hI hD i i p hd
  rw [modifiedSigma_contact_dzMii hU hu a b hneg hA hx i d hI hD hd hgap hc, hd] at hr
  simp only [Complex.ofReal_one, one_mul] at hr
  linear_combination hr

end PowerConvexity
