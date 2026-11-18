import PowerConvexity.Calculus.ModifiedPencilTwo
import PowerConvexity.Calculus.NormalizedContactColumn

/-! # Actual simple-root derivatives at a zero critical contact -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_ofReal_eq_zero_of_fderiv_eq_zero {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : fderiv ℝ f x = 0) (v w : E) :
    dz v w (fun y => (f y:ℂ)) x = 0 := by
  have he := complexGradient_real_entry hf (fun _ : Fin 1 => v) (fun _ : Fin 1 => w) 0
  change dz v w (fun y => (f y:ℂ)) x = _ at he
  rw [he,hc]
  simp

theorem modifiedSchur_dzbar_eq_star_swap {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (i j q : Fin 2) :
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
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hm

theorem modifiedSigmaTwo_contact_dzM00 {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) (v w : E) :
    dz v w (fun y => modifiedSchur a b u y 0 0) x = 0 := by
  have hd0 : 0 ≤ d 0 := by rw [hd]; norm_num
  have ho : d 1 < d 0 := by rwa [hd]
  obtain ⟨hσ,hg,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have hz : modifiedSigmaTwo a b u x = 0 := by simpa [hd] using hσ
  have hs := modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) hg
  have he := modifiedSigmaTwo_dz_normalized_exact hU hu a b hneg hA hx d hI hD hd0 hd1 ho v w
  rw [dz_ofReal_eq_zero_of_fderiv_eq_zero (hs.differentiableAt (by norm_num)) hc,hz] at he
  simpa using he.symm

theorem modifiedSigmaTwo_contact_mixed {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) (p q : Fin 2) :
    dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x =
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedSchur a b u y 0 0)) x-
      (dz (a p) (b p) (fun y => modifiedSchur a b u y 0 1) x*
        star (dz (a q) (b q) (fun y => modifiedSchur a b u y 0 1) x)+
       dz (a p) (b p) (fun y => modifiedSchur a b u y 1 0) x*
        star (dz (a q) (b q) (fun y => modifiedSchur a b u y 1 0) x))/
      ((1-d 1^2:ℝ):ℂ) := by
  have hd0 : 0 ≤ d 0 := by rw [hd]; norm_num
  have ho : d 1 < d 0 := by rwa [hd]
  obtain ⟨hσ,hg,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have hz : modifiedSigmaTwo a b u x = 0 := by simpa [hd] using hσ
  have hs := modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) hg
  have he := modifiedSigmaTwo_mixed_normalized_exact hU hu a b hneg hA hx d hI hD hd0 hd1 ho
    (a p) (b p) (a q) (-b q)
  simp only [dz_ofReal_eq_zero_of_fderiv_eq_zero (hs.differentiableAt (by norm_num)) hc,
    hz,Complex.ofReal_zero,zero_mul,sub_zero,hd,one_pow] at he
  rw [modifiedSchur_dzbar_eq_star_swap hU hu a b hneg hA hx 1 0 q,
    modifiedSchur_dzbar_eq_star_swap hU hu a b hneg hA hx 0 1 q] at he
  convert he using 1 <;> ring

theorem modifiedCompensated_contact_first_column {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : d 0 = 1) (hd1 : 0 ≤ d 1) (h1 : d 1 < 1)
    (hc : fderiv ℝ (modifiedSigmaTwo a b u) x = 0) (p : Fin 2) :
    modifiedCompensatedHessian a b u p x 0 0 = skewThirdHessian a b u 0 x p 0+
      (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))*
        (1 : Matrix (Fin 2) (Fin 2) ℂ) p 0 := by
  have hr := modifiedSchur_dz_contact_row (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b
    (hA x hx) d hI hD 0 0 p hd
  rw [modifiedSigmaTwo_contact_dzM00 hU hu a b hneg hA hx d hI hD hd hd1 h1 hc,hd] at hr
  simp only [Complex.ofReal_one,one_mul] at hr
  linear_combination hr

end PowerConvexity
