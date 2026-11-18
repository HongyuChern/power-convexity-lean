import PowerConvexity.Calculus.ConvexHessian
import PowerConvexity.Calculus.AppendixCConvexity

/-! # Nonnegative Hessians and the scalar convexity input in Appendix C -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem posSemidef_real_smul_iff (M : Matrix ι ι ℂ) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • M).PosSemidef ↔ M.PosSemidef := by
  have hc0 : 0 ≤ (c : ℂ) := by exact_mod_cast hc.le
  have hci : 0 ≤ ((c⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.mpr hc).le
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  constructor
  · intro h
    have hi := h.smul hci
    simpa only [Complex.ofReal_inv, smul_smul, inv_mul_cancel₀ hcn, one_smul] using hi
  · intro h
    exact h.smul hc0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_power_posSemidef_iff_modifiedSchur {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (realBlockHessian a b (powerTransform u) x).PosSemidef ↔
      (modifiedSchur a b u x).PosSemidef := by
  have hAv : (complexHessian a b (powerTransform u) x).PosDef := by
    rw [power_mixed_matrix hu hx]
    exact posDef_real_smul (modifiedA_posDef a b hx hA) (sqrtSlope_pos hx)
  obtain ⟨hReal, hSchur⟩ :=
    realBlockHessian_posSemidef_equivalences (powerTransform_contDiffAt hu hx) a b hAv
  have h := hReal.trans hSchur
  rw [schurHessian_powerTransform hu hx a b hA] at h
  exact h.trans (posSemidef_real_smul_iff _ (sqrtSlope_pos hx))

theorem modifiedSchur_scalar_posSemidef_iff {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) (hαpos : 0 < (scalarAlpha a b u x).re) :
    (modifiedSchur (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x).PosSemidef ↔
      0 ≤ scalarSigma a b u x := by
  have hα : scalarAlpha a b u x ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hαpos
    exact (lt_irrefl 0) hαpos
  rw [modifiedSchur_scalar_diagonal hu a b hα, Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    have hp : 0 ≤ (scalarAlpha a b u x).re * scalarSigma a b u x := by exact_mod_cast h 0
    exact (mul_nonneg_iff_of_pos_left hαpos).mp hp
  · intro h i
    exact_mod_cast mul_nonneg hαpos.le h

theorem scalarSigma_nonneg_of_convex_power {u : E → ℝ} {U : Set E} {ρ : ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hneg : ∀ x ∈ U, u x < 0)
    (hconv : ConvexOn ℝ U (powerTransform u)) (a b : E) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u x 0 0 = (ρ : ℂ)) {x : E} (hx : x ∈ U) :
    0 ≤ scalarSigma a b u x := by
  have hu2 := hu.contDiffAt (hU.mem_nhds hx)
  have hH := realBlockHessian_posSemidef_of_convexOn hU
    (powerTransform_contDiffOn hu hneg) hconv hx (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
  have hM := (realHessian_power_posSemidef_iff_modifiedSchur hu2 (hneg x hx) _ _
    (mixedHessian_scalar_posDef_of_density a b hρpos (hρ x hx))).mp hH
  exact (modifiedSchur_scalar_posSemidef_iff hu2 a b
    (scalarAlpha_re_pos_of_density (hneg x hx) a b hρpos (hρ x hx))).mp hM

end PowerConvexity
