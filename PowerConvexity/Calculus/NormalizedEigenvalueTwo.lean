import PowerConvexity.Calculus.EigenvalueFieldTwo
import PowerConvexity.Calculus.StrictConvexity

/-! # Normalized two-dimensional spectral calculation and the public convexity bridge -/

set_option autoImplicit false
open scoped ContDiff ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSchur_posSemidef_iff_sigmaTwo_nonneg {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    (modifiedSchur a b u x).PosSemidef ↔ 0 ≤ modifiedSigmaTwo a b u x :=
  schur_posSemidef_iff_lower_nonneg (modifiedA_posDef a b hx hA)
    (modifiedB_transpose hu a b)

theorem modifiedSchur_posDef_iff_sigmaTwo_pos {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    (modifiedSchur a b u x).PosDef ↔ 0 < modifiedSigmaTwo a b u x :=
  schur_posDef_iff_lower_pos (modifiedA_posDef a b hx hA)
    (modifiedB_transpose hu a b)

theorem modifiedK_normalized_diagonal {u : E → ℝ} {x : E}
    (a b : Fin 2 → E) (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i : ℂ))) :
    modifiedK a b u x = Matrix.diagonal (fun i => ((1 - d i^2 : ℝ) : ℂ)) := by
  unfold modifiedK modifiedSchur
  rw [hI, hD, inv_one, Matrix.mul_one, matrixSchur_one_real_diagonal]

theorem normalized_spectrumTwo_data {u : E → ℝ} {x : E}
    (a b : Fin 2 → E) (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i : ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (horder : d 1 < d 0) :
    modifiedSigmaTwo a b u x = 1 - d 0^2 ∧
      0 < eigenDiscriminantTwo (modifiedK a b u x) ∧
      modifiedK a b u x 0 0 = (modifiedSigmaTwo a b u x : ℂ) ∧
      modifiedK a b u x 0 1 = 0 ∧ modifiedK a b u x 1 0 = 0 ∧
      modifiedK a b u x 1 1 - (modifiedSigmaTwo a b u x : ℂ) ≠ 0 := by
  have hsq : d 1^2 < d 0^2 := (sq_lt_sq₀ hd1 hd0).mpr horder
  have hm : 1 - d 0^2 < 1 - d 1^2 := by linarith
  have hK := modifiedK_normalized_diagonal a b d hI hD
  have hσ : modifiedSigmaTwo a b u x = 1 - d 0^2 := by
    unfold modifiedSigmaTwo
    rw [hK, lowerEigenvalueTwo_real_diagonal, min_eq_left hm.le]
  refine ⟨hσ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK, eigenDiscriminantTwo_real_diagonal]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hm.ne)
  · rw [hK, hσ]
    simp
  · rw [hK]
    simp
  · rw [hK]
    simp
  · rw [hK, hσ]
    simp only [Matrix.diagonal_apply_eq]
    exact sub_ne_zero.mpr (fun h => hm.ne' (Complex.ofReal_injective h))

/-- The actual two-term formula `3.2-1` in the manuscript's normalized frame. -/
theorem modifiedSigmaTwo_mixed_normalized {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i : ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (horder : d 1 < d 0) (p q : Fin 2) :
    dz (a q) (-b q) (dz (a p) (b p)
        (fun y => (modifiedSigmaTwo a b u y : ℂ))) x =
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedK a b u y 0 0)) x -
      (dz (a p) (b p) (fun y => modifiedK a b u y 0 1) x *
          dz (a q) (-b q) (fun y => modifiedK a b u y 1 0) x +
        dz (a q) (-b q) (fun y => modifiedK a b u y 0 1) x *
          dz (a p) (b p) (fun y => modifiedK a b u y 1 0) x) /
      ((d 0^2 - d 1^2 : ℝ) : ℂ) := by
  obtain ⟨hσ, hg, h00, h01, h10, hden⟩ :=
    normalized_spectrumTwo_data a b d hI hD hd0 hd1 horder
  have h := modifiedSigmaTwo_mixed hU hu a b hneg hA hx hg h00 h01 h10 hden
    (a p) (b p) (a q) (-b q)
  have he : modifiedK a b u x 1 1 - (modifiedSigmaTwo a b u x : ℂ) =
      ((d 0^2 - d 1^2 : ℝ) : ℂ) := by
    rw [modifiedK_normalized_diagonal a b d hI hD, hσ]
    simp only [Matrix.diagonal_apply_eq, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_pow]
    ring
  rwa [he] at h

/-- A positive lowest eigenvalue supplies the public strict chord inequality.
The global PDE argument proving that positivity is not assumed to be complete. -/
theorem strictConvexOn_power_of_sigmaTwo_pos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ContDiffOn ℝ 2 u U)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E) (hneg : ∀ x ∈ U, u x < 0)
    (hA : ∀ x ∈ U,
      (complexHessian (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosDef)
    (hσ : ∀ x ∈ U,
      0 < modifiedSigmaTwo (fun i => e (.inl i)) (fun i => e (.inr i)) u x) :
    StrictConvexOn ℝ U (powerTransform u) := by
  apply strictConvexOn_power_of_modifiedSchur hU hconv hu e hneg hA
  intro x hx
  exact (modifiedSchur_posDef_iff_sigmaTwo_pos (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) _ _ (hA x hx)).mpr (hσ x hx)

end PowerConvexity
