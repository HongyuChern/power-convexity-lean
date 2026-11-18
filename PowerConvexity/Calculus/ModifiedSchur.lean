import PowerConvexity.Calculus.PowerTransform

/-!
# Modified Hessians and their actual Schur complement

These are the matrices `𝒜`, `ℬ`, and `ℳ` in frozen manuscript §2.2.  The last
theorem concerns positive definiteness of the real Hessian.  A global strict
convexity conclusion still requires the line-segment calculus bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder ContDiff

namespace PowerConvexity

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

noncomputable def modifiedA (a b : ι → E) (u : E → ℝ) (x : E) : Matrix ι ι ℂ :=
  fun i j => complexHessian a b u x i j +
    complexGradient a b u x i * star (complexGradient a b u x j) /
      ((2 * (-u x) : ℝ) : ℂ)

noncomputable def modifiedB (a b : ι → E) (u : E → ℝ) (x : E) : Matrix ι ι ℂ :=
  fun i j => pureHessian a b u x i j +
    complexGradient a b u x i * complexGradient a b u x j /
      ((2 * (-u x) : ℝ) : ℂ)

theorem power_mixed_matrix {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) :
    complexHessian a b (powerTransform u) x =
      (sqrtSlope (u x) : ℂ) • modifiedA a b u x := by
  ext i j
  exact complexHessian_powerTransform hu hx a b i j

theorem power_pure_matrix {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) :
    pureHessian a b (powerTransform u) x =
      (sqrtSlope (u x) : ℂ) • modifiedB a b u x := by
  ext i j
  exact pureHessian_powerTransform hu hx a b i j

theorem modifiedA_eq_rankOne (a b : ι → E) (u : E → ℝ) (x : E) :
    modifiedA a b u x = complexHessian a b u x +
      ((1 / (2 * (-u x)) : ℝ) : ℂ) •
        Matrix.vecMulVec (complexGradient a b u x) (star (complexGradient a b u x)) := by
  ext i j
  change complexHessian a b u x i j +
      complexGradient a b u x i * star (complexGradient a b u x j) /
        ((2 * (-u x) : ℝ) : ℂ) =
    complexHessian a b u x i j + ((1 / (2 * (-u x)) : ℝ) : ℂ) *
      (complexGradient a b u x i * star (complexGradient a b u x j))
  rw [Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem modifiedA_posDef [Fintype ι] {u : E → ℝ} {x : E}
    (a b : ι → E) (hx : u x < 0) (hA : (complexHessian a b u x).PosDef) :
    (modifiedA a b u x).PosDef := by
  rw [modifiedA_eq_rankOne]
  apply hA.add_posSemidef
  apply (Matrix.posSemidef_vecMulVec_self_star (complexGradient a b u x)).smul
  have h : 0 ≤ (1 / (2 * (-u x)) : ℝ) :=
    le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) (neg_pos.mpr hx)))
  exact_mod_cast h

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- Positive real scalar multiplication preserves positive definiteness. -/
theorem posDef_real_smul {M : Matrix ι ι ℂ} (hM : M.PosDef) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • M).PosDef := by
  have hc0 : 0 ≤ (c : ℂ) := by exact_mod_cast le_of_lt hc
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  apply ((hM.posSemidef.smul hc0).posDef_iff_det_ne_zero).mpr
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hcn) (ne_of_gt hM.det_pos)

theorem posDef_real_smul_iff (M : Matrix ι ι ℂ) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • M).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    have h' := posDef_real_smul h (inv_pos.mpr hc)
    have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
    simpa only [Complex.ofReal_inv, smul_smul, inv_mul_cancel₀ hcn, one_smul] using h'
  · intro h
    exact posDef_real_smul h hc

noncomputable def matrixSchur (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A - B * (A.map star)⁻¹ * B.map star

noncomputable def modifiedSchur (a b : ι → E) (u : E → ℝ) (x : E) : Matrix ι ι ℂ :=
  matrixSchur (modifiedA a b u x) (modifiedB a b u x)

omit [Fintype ι] [DecidableEq ι] in
theorem map_star_real_smul (M : Matrix ι ι ℂ) (c : ℝ) :
    ((c : ℂ) • M).map star = (c : ℂ) • M.map star := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

/-- The common factor is to the first power in the Schur complement. -/
theorem matrixSchur_real_smul (A B : Matrix ι ι ℂ) (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) :
    matrixSchur ((c : ℂ) • A) ((c : ℂ) • B) = (c : ℂ) • matrixSchur A B := by
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hbar : A.map star = A.transpose := by
    ext i j
    exact hA.isHermitian.apply j i
  have hunit : IsUnit (A.map star).det := by
    rw [hbar, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hinv : ((c : ℂ) • A.map star)⁻¹ = (c : ℂ)⁻¹ • (A.map star)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul _ hunit, mul_inv_cancel₀ hcn, one_smul]
  unfold matrixSchur
  rw [map_star_real_smul, map_star_real_smul, hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hcn, mul_one, smul_sub]

/-- The actual Schur Hessian of `-sqrt(-u)` equals its positive scalar factor
times the paper's modified Schur matrix. -/
theorem schurHessian_powerTransform {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    schurHessian a b (powerTransform u) x =
      (sqrtSlope (u x) : ℂ) • modifiedSchur a b u x := by
  change matrixSchur (complexHessian a b (powerTransform u) x)
    (pureHessian a b (powerTransform u) x) = _
  rw [power_mixed_matrix hu hx, power_pure_matrix hu hx]
  exact matrixSchur_real_smul _ _ (modifiedA_posDef a b hx hA) (sqrtSlope_pos hx)

/-- The pointwise bridge used in §2.2.  This is a Hessian positivity statement,
not a redefinition of the public strict-convexity conclusion. -/
theorem realHessian_power_posDef_iff_modifiedSchur {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (realBlockHessian a b (powerTransform u) x).PosDef ↔
      (modifiedSchur a b u x).PosDef := by
  have hAv : (complexHessian a b (powerTransform u) x).PosDef := by
    rw [power_mixed_matrix hu hx]
    exact posDef_real_smul (modifiedA_posDef a b hx hA) (sqrtSlope_pos hx)
  obtain ⟨hReal, hSchur⟩ :=
    realBlockHessian_posDef_equivalences (powerTransform_contDiffAt hu hx) a b hAv
  have h := hReal.trans hSchur
  rw [schurHessian_powerTransform hu hx a b hA] at h
  exact h.trans (posDef_real_smul_iff _ (sqrtSlope_pos hx))

end Finite

end PowerConvexity
