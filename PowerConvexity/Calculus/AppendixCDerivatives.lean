import PowerConvexity.Calculus.ModifiedSecondDerivatives
import PowerConvexity.Calculus.ConstantDensityGradient

/-!
# The exact scalar differential identities in Appendix C

The complex dimension is one, with constant real directions a,b.  The local
equation is allowed to have any constant density: normalizing alpha to one
need not preserve the numerical density one.  The original Appendix equation
is recovered by choosing rho = 1.  No asymptotic equivalence is used here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_of_eventually_const {f : E → ℂ} {x : E} {c : ℂ}
    (hf : f =ᶠ[𝓝 x] fun _ => c) (a b : E) : dz a b f x = 0 := by
  rw [dz_congr_nhds hf, dz_const]

theorem dz_dz_of_eventually_const {f : E → ℂ} {x : E} {c : ℂ}
    (hf : f =ᶠ[𝓝 x] fun _ => c) (a b v w : E) :
    dz a b (dz v w f) x = 0 := by
  apply dz_of_eventually_const (c := 0)
  exact hf.eventuallyEq_nhds.mono fun _ hy => dz_of_eventually_const hy v w

theorem pureHessian_dzbar_eq_dz_mixed {ι : Type*} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i j q : ι) :
    dz (a q) (-b q) (fun y => pureHessian a b u y i j) x =
      dz (a j) (b j) (fun y => complexHessian a b u y i q) x :=
  third_reverse_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu)
    (a q) (-b q) (a i) (b i) (a j) (b j)

noncomputable def scalarAlpha (a b : E) (u : E → ℝ) (x : E) : ℂ :=
  modifiedA (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0

noncomputable def scalarBeta (a b : E) (u : E → ℝ) (x : E) : ℂ :=
  modifiedB (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0

noncomputable def scalarSigma (a b : E) (u : E → ℝ) (x : E) : ℝ :=
  1 - Complex.normSq (scalarBeta a b u x) / (scalarAlpha a b u x).re ^ 2

theorem scalarAlpha_star {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    star (scalarAlpha a b u x) = scalarAlpha a b u x := by
  have h := (complexHessian_isHermitian hu (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b)).apply (0 : Fin 1) 0
  simp only [scalarAlpha, modifiedA_eq_weight, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj] at *
  rw [h]
  ring

/-- The exact identity `a(1-1)`; rho is the constant mixed Hessian. -/
theorem scalarAlpha_dz {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ) :
    dz a b (scalarAlpha a b u) x =
      (powerWeight (u x) : ℂ) * scalarBeta a b u x *
        star (dz a b (fun y => (u y : ℂ)) x) +
      (powerWeight (u x) : ℂ) * scalarAlpha a b u x *
        dz a b (fun y => (u y : ℂ)) x := by
  have h := modifiedA_dz hu hx (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0 0 0
  rw [dz_of_eventually_const hρ] at h
  change dz a b (scalarAlpha a b u) x = _ at h
  rw [h]
  simp only [scalarAlpha, scalarBeta, complexGradient]
  ring

/-- The exact first equality in `C(2.1)`. -/
theorem scalarBeta_dzbar {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ) :
    dz a (-b) (scalarBeta a b u) x =
      2 * (powerWeight (u x) : ℂ) * scalarAlpha a b u x *
        dz a b (fun y => (u y : ℂ)) x := by
  have h := modifiedB_dzbar hu hx (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0 0 0
  rw [pureHessian_dzbar_eq_dz_mixed hu (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0 0 0, dz_of_eventually_const hρ] at h
  change dz a (-b) (scalarBeta a b u) x = _ at h
  rw [h]
  simp only [scalarAlpha, complexGradient]
  ring

/-- The unlabelled exact second derivative of alpha after `C(2.1)`. -/
theorem scalarAlpha_dzbar_dz {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y : ℂ)) x
    let α := scalarAlpha a b u x
    let β := scalarBeta a b u x
    dz a (-b) (dz a b (scalarAlpha a b u)) x =
      h * (α^2 + (Complex.normSq β : ℂ)) +
      4 * h^2 * α * (Complex.normSq g : ℂ) +
      h^2 * β * (star g)^2 + h^2 * star β * g^2 := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have h := modifiedA_dzbar_dz hu hx (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0 0 0 0
  rw [dz_dz_of_eventually_const hρ, pureHessian_dzbar_eq_dz_mixed h3
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0 0 0,
    dz_of_eventually_const hρ, dz_of_eventually_const hρ] at h
  change dz a (-b) (dz a b (scalarAlpha a b u)) x = _ at h
  rw [h]
  simp only [scalarAlpha, scalarBeta, complexGradient,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- The unlabelled exact second derivative of beta before `C2.1.1`. -/
theorem scalarBeta_dz_dzbar {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y : ℂ)) x
    let α := scalarAlpha a b u x
    let β := scalarBeta a b u x
    dz a b (dz a (-b) (scalarBeta a b u)) x =
      2 * h * α * β + 4 * h^2 * α * g^2 +
        2 * h^2 * β * (Complex.normSq g : ℂ) := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 u y :=
    (hu.of_le (m := 3) (by norm_num)).eventually (by simp)
  have hB : (fun y => dz a (-b) (fun z => pureHessian
      (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u z 0 0) y) =ᶠ[𝓝 x]
        fun _ => (0 : ℂ) := by
    filter_upwards [hn, hρ.eventuallyEq_nhds] with y hy hyρ
    rw [pureHessian_dzbar_eq_dz_mixed hy (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) 0 0 0, dz_of_eventually_const hyρ]
  have h := modifiedB_dz_dzbar hu hx (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0 0 0 0
  rw [dz_of_eventually_const hB, dz_of_eventually_const hρ] at h
  change dz a b (dz a (-b) (scalarBeta a b u)) x = _ at h
  rw [h]
  simp only [scalarAlpha, scalarBeta, complexGradient,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end PowerConvexity
