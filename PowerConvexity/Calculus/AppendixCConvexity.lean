import PowerConvexity.Calculus.AppendixCGradientEstimate
import PowerConvexity.Calculus.StrictConvexity

/-! # Scalar sigma, the real Hessian, and the public strict chord inequality -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixSchur_fin_one_entry (A B : Matrix (Fin 1) (Fin 1) ℂ) :
    matrixSchur A B 0 0 = A 0 0 - B 0 0 * (star (A 0 0))⁻¹ * star (B 0 0) := by
  simp [matrixSchur, Matrix.mul_apply, Matrix.inv_subsingleton, Ring.inverse_eq_inv]

theorem modifiedSchur_scalar_diagonal {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) (hα : scalarAlpha a b u x ≠ 0) :
    modifiedSchur (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x =
      Matrix.diagonal (fun _ => (((scalarAlpha a b u x).re * scalarSigma a b u x : ℝ) : ℂ)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [Matrix.diagonal_apply_eq]
  change matrixSchur _ _ 0 0 = _
  rw [matrixSchur_fin_one_entry]
  change scalarAlpha a b u x - scalarBeta a b u x *
    (star (scalarAlpha a b u x))⁻¹ * star (scalarBeta a b u x) = _
  rw [Complex.ofReal_mul, scalarSigma_cast_eq_ratio hu a b,
    complex_ofReal_re_of_star_eq (scalarAlpha_star hu a b), scalarAlpha_star hu a b]
  simp only [scalarRatio, star_div₀, scalarAlpha_star hu a b]
  field_simp

theorem modifiedSchur_scalar_posDef_iff {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) (hαpos : 0 < (scalarAlpha a b u x).re) :
    (modifiedSchur (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x).PosDef ↔
      0 < scalarSigma a b u x := by
  have hα : scalarAlpha a b u x ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hαpos
    exact (lt_irrefl 0) hαpos
  rw [modifiedSchur_scalar_diagonal hu a b hα, Matrix.posDef_diagonal_iff]
  constructor
  · intro h
    have hp : 0 < (scalarAlpha a b u x).re * scalarSigma a b u x := by
      exact_mod_cast h 0
    exact (mul_pos_iff_of_pos_left hαpos).mp hp
  · intro h i
    exact_mod_cast mul_pos hαpos h

theorem mixedHessian_scalar_posDef_of_density {u : E → ℝ} {x : E} {ρ : ℝ}
    (a b : E) (hρpos : 0 < ρ)
    (hρ : complexHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0 = (ρ : ℂ)) :
    (complexHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x).PosDef := by
  have he : complexHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x =
      Matrix.diagonal (fun _ => (ρ : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using hρ
  rw [he, Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hρpos

theorem realHessian_power_scalar_posDef_iff {u : E → ℝ} {x : E} {ρ : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : E) (hρpos : 0 < ρ)
    (hρ : complexHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0 = (ρ : ℂ)) :
    (realBlockHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      (powerTransform u) x).PosDef ↔ 0 < scalarSigma a b u x := by
  rw [realHessian_power_posDef_iff_modifiedSchur hu hx _ _
    (mixedHessian_scalar_posDef_of_density a b hρpos hρ)]
  exact modifiedSchur_scalar_posDef_iff hu a b
    (scalarAlpha_re_pos_of_density hx a b hρpos hρ)

/-- The scalar public bridge retains sigma positivity as its explicit PDE input. -/
theorem strictConvexOn_power_of_scalarSigma_pos {u : E → ℝ} {U : Set E} {ρ : ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ContDiffOn ℝ 2 u U)
    (e : Module.Basis (Fin 1 ⊕ Fin 1) ℝ E) (hneg : ∀ x ∈ U, u x < 0)
    (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun i => e (.inl i))
      (fun i => e (.inr i)) u x 0 0 = (ρ : ℂ))
    (hσ : ∀ x ∈ U, 0 < scalarSigma (e (.inl 0)) (e (.inr 0)) u x) :
    StrictConvexOn ℝ U (powerTransform u) := by
  have hea : (fun i : Fin 1 => e (.inl i)) = fun _ => e (.inl 0) := by
    funext i
    fin_cases i
    rfl
  have heb : (fun i : Fin 1 => e (.inr i)) = fun _ => e (.inr 0) := by
    funext i
    fin_cases i
    rfl
  have hdensity := hρ
  rw [hea, heb] at hdensity
  apply strictConvexOn_power_of_modifiedSchur hU hconv hu e hneg
  · intro x hx
    rw [hea, heb]
    exact mixedHessian_scalar_posDef_of_density _ _ hρpos (hdensity x hx)
  · intro x hx
    rw [hea, heb]
    exact (modifiedSchur_scalar_posDef_iff (hu.contDiffAt (hU.mem_nhds hx)) _ _
      (scalarAlpha_re_pos_of_density (hneg x hx) _ _ hρpos (hdensity x hx))).mpr (hσ x hx)

end PowerConvexity
