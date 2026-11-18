import PowerConvexity.Algebra.ResidualAlgebra

/-! # Contracted second derivatives after actual constant-density cancellations -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem weighted_sum_cancel_two (W D₁ D₂ L S : ι → ι → ℂ) (c d : ℂ)
    (h₁ : (∑ p, ∑ q, W p q * D₁ p q) = 0)
    (h₂ : (∑ p, ∑ q, W p q * D₂ p q) = 0) :
    (∑ p, ∑ q, W p q * (L p q + c * D₁ p q + d * D₂ p q + S p q)) =
      (∑ p, ∑ q, W p q * L p q) + (∑ p, ∑ q, W p q * S p q) := by
  calc
    _ = (∑ p, ∑ q, W p q * L p q) + c * (∑ p, ∑ q, W p q * D₁ p q) +
        d * (∑ p, ∑ q, W p q * D₂ p q) + (∑ p, ∑ q, W p q * S p q) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by rw [h₁, h₂]; ring

theorem matrixDZ_modifiedA_correction {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (p : ι) :
    matrixDZ (a p) (b p) (modifiedA a b u) x =
      matrixDZ (a p) (b p) (complexHessian a b u) x +
        modificationAz (powerWeight (u x)) (complexGradient a b u x)
          (modifiedA a b u x) (modifiedB a b u x) p := by
  ext i j
  simpa only [matrixDZ, Matrix.add_apply, modificationAz, add_assoc] using
    modifiedA_dz hu hx a b i j p

theorem matrixDZbar_modifiedA_correction {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (q : ι) :
    matrixDZ (a q) (-b q) (modifiedA a b u) x =
      matrixDZ (a q) (-b q) (complexHessian a b u) x +
        modificationAbar (powerWeight (u x)) (complexGradient a b u x)
          (modifiedA a b u x) (modifiedB a b u x) q := by
  ext i j
  simpa only [matrixDZ, Matrix.add_apply, modificationAbar, add_assoc] using
    modifiedA_dzbar hu hx a b i j q

theorem matrixDZbar_modifiedB_correction {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (q : ι) :
    matrixDZ (a q) (-b q) (modifiedB a b u) x =
      matrixDZ (a q) (-b q) (pureHessian a b u) x +
        modificationBbar (powerWeight (u x)) (complexGradient a b u x)
          (modifiedA a b u x) q := by
  ext i j
  simpa only [matrixDZ, Matrix.add_apply, modificationBbar, add_assoc] using
    modifiedB_dzbar hu hx a b i j q

/-- `2_2_12` after the two third-derivative contractions are proved zero.
The original second matrix contraction is retained for subsequent PDE substitution. -/
theorem modifiedA_contracted_second {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ) :
    matrixL a b u (modifiedA a b u) x =
      matrixL a b u (complexHessian a b u) x +
        contract (complexHessian a b u x)⁻¹
          (modificationASecond (powerWeight (u x)) (complexGradient a b u x)
            (modifiedA a b u x) (modifiedB a b u x)) := by
  have hu3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  ext i j
  have he (p q : ι) :
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedA a b u y i j)) x =
        dz (a q) (-b q) (dz (a p) (b p) (fun y => complexHessian a b u y i j)) x +
        ((powerWeight (u x) : ℂ) * star (complexGradient a b u x j)) *
          dz (a q) (-b q) (fun y => pureHessian a b u y i p) x +
        ((powerWeight (u x) : ℂ) * complexGradient a b u x i) *
          dz (a q) (-b q) (fun y => complexHessian a b u y p j) x +
        modificationASecond (powerWeight (u x)) (complexGradient a b u x)
          (modifiedA a b u x) (modifiedB a b u x) p q i j := by
    rw [modifiedA_dzbar_dz hu hx]
    unfold modificationASecond
    ring
  simp only [matrixL, contract, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, matrixDZ, he]
  exact weighted_sum_cancel_two _ _ _ _ _ _ _
    (contracted_dzbar_pure_zero hu3 a b hdet i)
    (contracted_dzbar_mixed_zero hu3 a b hdet j)

/-- The second pure-matrix formula following `2_2_15`, with the contraction
in the same derivative order as `upqmpq`. -/
theorem modifiedB_contracted_second {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ) :
    matrixL a b u (modifiedB a b u) x =
      matrixL a b u (pureHessian a b u) x +
        contract (complexHessian a b u x)⁻¹
          (modificationBSecond (powerWeight (u x)) (complexGradient a b u x)
            (modifiedA a b u x) (modifiedB a b u x)) := by
  have hu3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  ext i j
  have he (p q : ι) :
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedB a b u y i j)) x =
        dz (a q) (-b q) (dz (a p) (b p) (fun y => pureHessian a b u y i j)) x +
        ((powerWeight (u x) : ℂ) * complexGradient a b u x j) *
          dz (a p) (b p) (fun y => complexHessian a b u y i q) x +
        ((powerWeight (u x) : ℂ) * complexGradient a b u x i) *
          dz (a p) (b p) (fun y => complexHessian a b u y j q) x +
        modificationBSecond (powerWeight (u x)) (complexGradient a b u x)
          (modifiedA a b u x) (modifiedB a b u x) p q i j := by
    rw [dz_comm_at (modifiedB_contDiffAt_two hu hx a b i j), modifiedB_dz_dzbar hu hx,
      dz_comm_at (pureHessian_contDiffAt_two hu a b i j) (a p) (b p) (a q) (-b q)]
    unfold modificationBSecond
    ring
  simp only [matrixL, contract, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, matrixDZ, he]
  exact weighted_sum_cancel_two _ _ _ _ _ _ _
    (contracted_dz_mixed_zero hu3 a b hdet i)
    (contracted_dz_mixed_zero hu3 a b hdet j)

end PowerConvexity
