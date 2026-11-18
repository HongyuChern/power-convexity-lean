import PowerConvexity.Calculus.ScalarQuotientCalculus
import PowerConvexity.Algebra.ScalarSigmaIdentity

/-! # The actual scalar ratio beta/alpha in Appendix C -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scalarRatio (a b : E) (u : E → ℝ) (x : E) : ℂ :=
  scalarBeta a b u x / scalarAlpha a b u x

theorem scalarAlpha_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E) :
    ContDiffAt ℝ 2 (scalarAlpha a b u) x :=
  modifiedA_contDiffAt_two hu hx (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0 0

theorem scalarBeta_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E) :
    ContDiffAt ℝ 2 (scalarBeta a b u) x :=
  modifiedB_contDiffAt_two hu hx (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0 0

theorem scalarRatio_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) : ContDiffAt ℝ 2 (scalarRatio a b u) x := by
  change ContDiffAt ℝ 2 (fun y => scalarBeta a b u y * (scalarAlpha a b u y)⁻¹) x
  exact (scalarBeta_contDiffAt_two hu hx a b).mul
    ((scalarAlpha_contDiffAt_two hu hx a b).inv hα)

theorem scalarSigma_eq_ratio {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    scalarSigma a b u x = 1 - Complex.normSq (scalarRatio a b u x) := by
  have hreal := complex_ofReal_re_of_star_eq (scalarAlpha_star hu a b)
  unfold scalarSigma scalarRatio
  rw [Complex.normSq_div, ← hreal, Complex.normSq_ofReal, pow_two]
  rfl

theorem scalarSigma_cast_eq_ratio {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    (scalarSigma a b u x : ℂ) =
      1 - scalarRatio a b u x * star (scalarRatio a b u x) := by
  rw [scalarSigma_eq_ratio hu a b]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]
  ring

theorem scalarSigma_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) : ContDiffAt ℝ 2 (scalarSigma a b u) x := by
  have hq := scalarRatio_contDiffAt_two hu hx a b hα
  have hr := Complex.reCLM.contDiff.contDiffAt.comp x hq
  have hi := Complex.imCLM.contDiff.contDiffAt.comp x hq
  have hnorm : ContDiffAt ℝ 2 (fun y => 1 - Complex.normSq (scalarRatio a b u y)) x := by
    simp only [Complex.normSq_apply]
    exact contDiffAt_const.sub ((hr.mul hr).add (hi.mul hi))
  apply hnorm.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y :=
    (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  exact hn.mono fun y hy => scalarSigma_eq_ratio hy a b

theorem scalarAlpha_dzbar {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ) :
    dz a (-b) (scalarAlpha a b u) x =
      (powerWeight (u x) : ℂ) * star (dz a b (fun y => (u y : ℂ)) x) *
        scalarAlpha a b u x +
      (powerWeight (u x) : ℂ) * dz a b (fun y => (u y : ℂ)) x *
        star (scalarBeta a b u x) := by
  have h := modifiedA_dzbar hu hx (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0 0 0
  rw [dz_of_eventually_const hρ] at h
  change dz a (-b) (scalarAlpha a b u) x = _ at h
  simpa only [zero_add, scalarAlpha, scalarBeta, complexGradient] using h

theorem scalarRatio_dzbar {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x ≠ 0) :
    dz a (-b) (scalarRatio a b u) x =
      (powerWeight (u x) : ℂ) *
        ((1 + (scalarSigma a b u x : ℂ)) * dz a b (fun y => (u y : ℂ)) x -
          scalarRatio a b u x * star (dz a b (fun y => (u y : ℂ)) x)) := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hd := dz_div_at
    ((scalarBeta_contDiffAt_two hu hx a b).differentiableAt (by norm_num))
    ((scalarAlpha_contDiffAt_two hu hx a b).differentiableAt (by norm_num)) hα a (-b)
  change dz a (-b) (scalarRatio a b u) x = _ at hd
  rw [hd, scalarBeta_dzbar h3 hx a b hρ, scalarAlpha_dzbar h3 hx a b hρ,
    scalarSigma_cast_eq_ratio h2 a b]
  simp only [scalarRatio, star_div₀, scalarAlpha_star h2 a b]
  field_simp
  ring

end PowerConvexity
