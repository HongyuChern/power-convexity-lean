import PowerConvexity.Calculus.AppendixCSigmaEquation

/-! # Literal normalized Appendix C identities with exact remainders

The normalization is at one fixed point, never differentiated. Constant density
is retained after the fixed change of coordinates. The C3.1 sign at frozen line
1847 is corrected: the leading compensated field is h (u_z - u_barz).
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scalarCompensated (a b : E) (u : E → ℝ) (x : E) : ℂ :=
  dz a b (scalarBeta a b u) x -
    scalarBeta a b u x * dz a b (scalarAlpha a b u) x / scalarAlpha a b u x

theorem scalarCompensated_eq_alpha_mul_ratio_derivative {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    scalarCompensated a b u x = scalarAlpha a b u x * dz a b (scalarRatio a b u) x := by
  have hd := dz_div_at
    ((scalarBeta_contDiffAt_two hu hx a b).differentiableAt (by norm_num))
    ((scalarAlpha_contDiffAt_two hu hx a b).differentiableAt (by norm_num)) hα a b
  change dz a b (scalarRatio a b u) x = _ at hd
  rw [hd]
  unfold scalarCompensated
  field_simp
  <;> ring

theorem scalarSigma_normalized_value {u : E → ℝ} {x : E} (a b : E) (β : ℝ)
    (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    scalarSigma a b u x = 1-β^2 := by
  simp only [scalarSigma, hα, hβ, Complex.one_re, one_pow, div_one, Complex.normSq_ofReal]
  ring

theorem scalarAlpha_normalized_first_remainder {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    dz a b (scalarAlpha a b u) x-h*(star g+g) = h*((β:ℂ)-1)*star g := by
  dsimp only
  rw [scalarAlpha_dz hu hx a b hρ, hα, hβ]
  ring

/-- C2.1.1 with its exact sigma remainder. -/
theorem scalar_C211_normalized_remainder {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    dz a (-b) (dz a b (scalarAlpha a b u)) x -
      dz a b (scalarAlpha a b u) x * dz a (-b) (scalarAlpha a b u) x -
      (2*h+2*h^2*(Complex.normSq g:ℂ)) =
    -(scalarSigma a b u x:ℂ)*(h-h^2*(Complex.normSq g:ℂ)) := by
  dsimp only
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  rw [scalarAlpha_dzbar_dz hu hx a b hρ, scalarAlpha_dz h3 hx a b hρ,
    scalarAlpha_dzbar h3 hx a b hρ, scalarSigma_normalized_value a b β hα hβ, hα, hβ]
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  ring

/-- C2.1.2 with the corrected g^2 + conjugate(g)^2 and an exact remainder. -/
theorem scalar_C212_normalized_remainder {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    dz a (-b) (dz a b (scalarAlpha a b u)) x -
      dz a (-b) (scalarBeta a b u) x *
        dz a b (fun y => star (scalarBeta a b u y)) x -
      (2*h+h^2*(g^2+(star g)^2)) =
    ((β:ℂ)-1)*(h*((β:ℂ)+1)+h^2*(g^2+(star g)^2)) := by
  dsimp only
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  rw [scalarAlpha_dzbar_dz hu hx a b hρ, dz_star_reverse,
    scalarBeta_dzbar h3 hx a b hρ, hα, hβ]
  simp only [star_mul, star_one, star_ofNat, Complex.star_def, Complex.conj_ofReal,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- C2.1.3 uses the actual commuting mixed derivatives of beta. -/
theorem scalar_C213_normalized_remainder {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    dz a (-b) (dz a b (scalarBeta a b u)) x -
      dz a b (scalarAlpha a b u) x * dz a (-b) (scalarBeta a b u) x -
      (2*h+2*h^2*g^2) = 2*h*((β:ℂ)-1) := by
  dsimp only
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  rw [dz_comm_at (scalarBeta_contDiffAt_two hu hx a b),
    scalarBeta_dz_dzbar hu hx a b hρ, scalarAlpha_dz h3 hx a b hρ,
    scalarBeta_dzbar h3 hx a b hρ, hα, hβ]
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Corrected C3.1, before division by beta. All terms are actual derivatives. -/
theorem scalar_C31_normalized_gradient_remainder {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ)) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    let σ : ℂ := scalarSigma a b u x
    (β:ℂ)*(scalarCompensated a b u x-h*(g-star g)) =
      -dz a b (fun y => (scalarSigma a b u y:ℂ)) x -
      (β:ℂ)*h*σ*star g+(β:ℂ)*h*((β:ℂ)-1)*g := by
  dsimp only
  have hne : scalarAlpha a b u x ≠ 0 := by rw [hα]; exact one_ne_zero
  have hq : scalarRatio a b u x = (β:ℂ) := by simp [scalarRatio,hα,hβ]
  have hc : scalarCompensated a b u x = dz a b (scalarRatio a b u) x := by
    rw [scalarCompensated_eq_alpha_mul_ratio_derivative hu hx a b hne,hα,one_mul]
  rw [hc, scalarSigma_dz hu hx a b hne, scalarRatio_dzbar hu hx a b hρ hne, hq]
  simp only [star_mul,star_sub,star_add,star_one,star_star,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
  ring

/-- At normalized zero critical contact the sign in frozen C3.1 is reversed. -/
theorem scalarCompensated_corrected_contact {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = 1)
    (hs : dz a b (fun y => (scalarSigma a b u y:ℂ)) x = 0) :
    scalarCompensated a b u x = (powerWeight (u x):ℂ)*
      (dz a b (fun y => (u y:ℂ)) x-star (dz a b (fun y => (u y:ℂ)) x)) := by
  have h := scalar_C31_normalized_gradient_remainder hu hx a b hρ 1 hα (by simpa using hβ)
  have hσ := scalarSigma_normalized_value a b 1 hα (by simpa using hβ)
  norm_num at hσ
  apply sub_eq_zero.mp
  simpa [hs,hσ] using h

theorem scalar_normalized_beta_error_le_sigma {u : E → ℝ} {x : E} (a b : E)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ))
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 ≤ scalarSigma a b u x ∧ ‖(β:ℂ)-1‖ ≤ scalarSigma a b u x := by
  rw [scalarSigma_normalized_value a b β hα hβ]
  have hb : ‖(β:ℂ)-1‖ = 1-β := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hβ1)]
    ring
  rw [hb]
  constructor <;> nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hβ1)]

/-- One downstream call collects actual C(1.1), C2.1.1--3 with controlled errors.
The coefficients are explicit; no asymptotic equality is assumed. -/
theorem scalar_normalized_paper_residual_bounds {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ))
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    let σ := scalarSigma a b u x
    ‖dz a b (scalarAlpha a b u) x-h*(star g+g)‖ ≤ σ*‖h*star g‖ ∧
    ‖dz a (-b) (dz a b (scalarAlpha a b u)) x -
      dz a b (scalarAlpha a b u) x * dz a (-b) (scalarAlpha a b u) x -
      (2*h+2*h^2*(Complex.normSq g:ℂ))‖ ≤ σ*‖h-h^2*(Complex.normSq g:ℂ)‖ ∧
    ‖dz a (-b) (dz a b (scalarAlpha a b u)) x -
      dz a (-b) (scalarBeta a b u) x *
        dz a b (fun y => star (scalarBeta a b u y)) x -
      (2*h+h^2*(g^2+(star g)^2))‖ ≤ σ*‖h*((β:ℂ)+1)+h^2*(g^2+(star g)^2)‖ ∧
    ‖dz a (-b) (dz a b (scalarBeta a b u)) x -
      dz a b (scalarAlpha a b u) x * dz a (-b) (scalarBeta a b u) x -
      (2*h+2*h^2*g^2)‖ ≤ σ*‖2*h‖ := by
  dsimp only
  obtain ⟨hσ,herr⟩ := scalar_normalized_beta_error_le_sigma a b β hα hβ hβ0 hβ1
  have hcoeff (c : ℂ) : ‖((β:ℂ)-1)*c‖ ≤ scalarSigma a b u x*‖c‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right herr (norm_nonneg c)
  have hsigmanorm : ‖(scalarSigma a b u x:ℂ)‖ = scalarSigma a b u x :=
    Complex.norm_of_nonneg hσ
  rw [scalarAlpha_normalized_first_remainder (hu.of_le (by norm_num)) hx a b hρ β hα hβ,
    scalar_C211_normalized_remainder hu hx a b hρ β hα hβ,
    scalar_C212_normalized_remainder hu hx a b hρ β hα hβ,
    scalar_C213_normalized_remainder hu hx a b hρ β hα hβ]
  refine ⟨?_,?_,hcoeff _,?_⟩
  · convert hcoeff ((powerWeight (u x):ℂ)*star (dz a b (fun y => (u y:ℂ)) x)) using 1 <;> congr 1 <;> ring
  · simp only [norm_mul,norm_neg,hsigmanorm,le_refl]
  · simpa only [mul_comm] using hcoeff (2*(powerWeight (u x):ℂ))

/-- Quantitative corrected C3.1 on the positive near-contact branch beta >= 1/2. -/
theorem scalar_C31_normalized_error_bound {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (β : ℝ) (hα : scalarAlpha a b u x = 1) (hβ : scalarBeta a b u x = (β:ℂ))
    (hβ0 : 1/2 ≤ β) (hβ1 : β ≤ 1) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y:ℂ)) x
    ‖scalarCompensated a b u x-h*(g-star g)‖ ≤
      2*‖dz a b (fun y => (scalarSigma a b u y:ℂ)) x‖ +
      2*‖h‖*‖g‖*scalarSigma a b u x := by
  let h : ℂ := powerWeight (u x)
  let g := dz a b (fun y => (u y:ℂ)) x
  let σ := scalarSigma a b u x
  let s := dz a b (fun y => (scalarSigma a b u y:ℂ)) x
  let R := scalarCompensated a b u x-h*(g-star g)
  have hb : 0 < β := by linarith
  obtain ⟨hσ,herr⟩ := scalar_normalized_beta_error_le_sigma a b β hα hβ hb.le hβ1
  change 0 ≤ σ at hσ
  change ‖(β:ℂ)-1‖ ≤ σ at herr
  have he : (β:ℂ)*R = -s-(β:ℂ)*h*(σ:ℂ)*star g+(β:ℂ)*h*((β:ℂ)-1)*g :=
    scalar_C31_normalized_gradient_remainder hu hx a b hρ β hα hβ
  have hbn : ‖(β:ℂ)‖ = β := Complex.norm_of_nonneg hb.le
  have hsn : ‖(σ:ℂ)‖ = σ := Complex.norm_of_nonneg hσ
  have hN : β*‖R‖ ≤ ‖s‖+β*‖h‖*σ*‖g‖+β*‖h‖*‖(β:ℂ)-1‖*‖g‖ := by
    calc
      β*‖R‖ = ‖(β:ℂ)*R‖ := by rw [norm_mul,hbn]
      _ = ‖-s-(β:ℂ)*h*(σ:ℂ)*star g+(β:ℂ)*h*((β:ℂ)-1)*g‖ := by rw [he]
      _ ≤ ‖-s-(β:ℂ)*h*(σ:ℂ)*star g‖+‖(β:ℂ)*h*((β:ℂ)-1)*g‖ := norm_add_le _ _
      _ ≤ (‖-s‖+‖(β:ℂ)*h*(σ:ℂ)*star g‖)+‖(β:ℂ)*h*((β:ℂ)-1)*g‖ := by
        linarith [norm_sub_le (-s) ((β:ℂ)*h*(σ:ℂ)*star g)]
      _ = _ := by simp only [norm_neg,norm_mul,norm_star,hbn,hsn]
  have hm : β*‖h‖*‖(β:ℂ)-1‖*‖g‖ ≤ β*‖h‖*σ*‖g‖ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left herr (mul_nonneg hb.le (norm_nonneg h))) (norm_nonneg g)
  change ‖R‖ ≤ 2*‖s‖+2*‖h‖*‖g‖*σ
  have hns : ‖s‖ ≤ 2*β*‖s‖ := by nlinarith [norm_nonneg s]
  have hbR : β*‖R‖ ≤ β*(2*‖s‖+2*‖h‖*‖g‖*σ) := by nlinarith
  exact (mul_le_mul_iff_right₀ hb).mp hbR

noncomputable def scalarMu (a b : E) (u : E → ℝ) (x : E) : ℂ :=
  scalarAlpha a b u x -
    scalarBeta a b u x * star (scalarBeta a b u x) / scalarAlpha a b u x

theorem scalarMu_eq_alpha_sigma {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    scalarMu a b u x = scalarAlpha a b u x*(scalarSigma a b u x:ℂ) := by
  by_cases hα : scalarAlpha a b u x = 0
  · simp [scalarMu,hα]
  rw [scalarSigma_cast_eq_ratio hu a b]
  unfold scalarMu scalarRatio
  rw [star_div₀,scalarAlpha_star hu a b]
  field_simp
  <;> ring

/-- The literal actual first Schur derivative a(2-2). -/
theorem scalarMu_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    dz a b (scalarMu a b u) x = dz a b (scalarAlpha a b u) x -
      scalarCompensated a b u x*star (scalarBeta a b u x)/scalarAlpha a b u x -
      scalarBeta a b u x*dz a b (fun y => star (scalarBeta a b u y)) x/scalarAlpha a b u x := by
  have hA := (scalarAlpha_contDiffAt_two hu hx a b).differentiableAt (by norm_num)
  have hB := (scalarBeta_contDiffAt_two hu hx a b).differentiableAt (by norm_num)
  have hi : DifferentiableAt ℝ (fun y => (scalarAlpha a b u y)⁻¹) x := hA.inv hα
  have hprod : DifferentiableAt ℝ (fun y => scalarBeta a b u y*star (scalarBeta a b u y)) x :=
    hB.mul hB.star
  have hdiv : DifferentiableAt ℝ (fun y => scalarBeta a b u y*
      star (scalarBeta a b u y)/scalarAlpha a b u y) x := by
    simpa only [div_eq_mul_inv,Pi.mul_def] using hprod.mul hi
  have hsub := dz_sub_at hA hdiv a b
  have hd := dz_div_at (hB.mul hB.star) hA hα a b
  have hp := dz_mul_at hB hB.star a b
  simp only [Pi.sub_def,Pi.mul_def] at hsub hd hp
  change dz a b (fun y => scalarAlpha a b u y-
    scalarBeta a b u y*star (scalarBeta a b u y)/scalarAlpha a b u y) x = _
  rw [hsub,hd,hp]
  unfold scalarCompensated
  field_simp
  <;> ring

theorem scalarMu_dz_eq_sigma_product {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    dz a b (scalarMu a b u) x = scalarAlpha a b u x*
      dz a b (fun y => (scalarSigma a b u y:ℂ)) x +
      (scalarSigma a b u x:ℂ)*dz a b (scalarAlpha a b u) x := by
  have hn := (hu.of_le (m:=2) (by norm_num)).eventually (by simp)
  have he : scalarMu a b u =ᶠ[𝓝 x] fun y => scalarAlpha a b u y*(scalarSigma a b u y:ℂ) :=
    hn.mono fun y hy => scalarMu_eq_alpha_sigma hy a b
  have hS := Complex.ofRealCLM.differentiableAt.comp x
    ((scalarSigma_contDiffAt_two hu hx a b hα).differentiableAt (by norm_num))
  change DifferentiableAt ℝ (fun y => (scalarSigma a b u y:ℂ)) x at hS
  rw [dz_congr_nhds he, dz_mul_at
    ((scalarAlpha_contDiffAt_two hu hx a b).differentiableAt (by norm_num)) hS]
  ring

/-- The literal actual quotient derivative a(2-1), before error notation. -/
theorem scalarSigma_dz_from_mu {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    dz a b (fun y => (scalarSigma a b u y:ℂ)) x =
      dz a b (scalarMu a b u) x/scalarAlpha a b u x -
      scalarMu a b u x*dz a b (scalarAlpha a b u) x/(scalarAlpha a b u x)^2 := by
  rw [scalarMu_dz_eq_sigma_product hu hx a b hα,
    scalarMu_eq_alpha_sigma (hu.of_le (by norm_num)) a b]
  field_simp
  <;> ring

theorem scalarMu_mixed_eq_sigma_product {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    let S : E → ℂ := fun y => scalarSigma a b u y
    dz a (-b) (dz a b (scalarMu a b u)) x =
      dz a (-b) (dz a b (scalarAlpha a b u)) x*S x +
      dz a b (scalarAlpha a b u) x*dz a (-b) S x +
      dz a (-b) (scalarAlpha a b u) x*dz a b S x +
      scalarAlpha a b u x*dz a (-b) (dz a b S) x := by
  have hn := (hu.of_le (m:=2) (by norm_num)).eventually (by simp)
  have he : scalarMu a b u =ᶠ[𝓝 x] fun y => scalarAlpha a b u y*(scalarSigma a b u y:ℂ) :=
    hn.mono fun y hy => scalarMu_eq_alpha_sigma hy a b
  have hS := Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (scalarSigma_contDiffAt_two hu hx a b hα)
  rw [dz_dz_congr_nhds he]
  exact dz_mixed_mul_at (scalarAlpha_contDiffAt_two hu hx a b) hS a b a (-b)

/-- The valid zero-critical-contact conclusion at frozen lines 1857--1865.
This downstream call uses the actual mu/sigma product and exact scalar PDE. -/
theorem scalarMu_mixed_zero_at_sigma_critical_zero {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x ≠ 0) (hσ : scalarSigma a b u x = 0)
    (hs : dz a b (fun y => (scalarSigma a b u y:ℂ)) x = 0) :
    dz a (-b) (dz a b (scalarMu a b u)) x = 0 ∧
      dz a (-b) (dz a b (fun y => (scalarSigma a b u y:ℂ))) x = 0 := by
  have hr := scalarSigma_cast_eq_ratio (hu.of_le (by norm_num)) a b
  rw [hσ,Complex.ofReal_zero] at hr
  have hR : scalarRatio a b u x*star (scalarRatio a b u x) = 1 := by
    linear_combination hr
  have he := scalarSigma_equation_complex hu hx a b hρ hα
  dsimp only at he
  rw [hR,hσ,hs] at he
  have hmix : dz a (-b) (dz a b (fun y => (scalarSigma a b u y:ℂ))) x = 0 := by
    simpa using he
  have hsbar : dz a (-b) (fun y => (scalarSigma a b u y:ℂ)) x = 0 := by
    have hh := dz_star_reverse a (-b) (fun y => (scalarSigma a b u y:ℂ)) x
    simp only [neg_neg,Complex.star_def,Complex.conj_ofReal,hs,map_zero] at hh
    exact hh
  refine ⟨?_,hmix⟩
  rw [scalarMu_mixed_eq_sigma_product hu hx a b hα]
  simp [hσ,hs,hsbar,hmix]

end PowerConvexity
