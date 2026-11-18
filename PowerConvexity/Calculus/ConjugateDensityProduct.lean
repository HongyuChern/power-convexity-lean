import PowerConvexity.Calculus.ConjugateContraction

/-! # Constant-density products for the two conjugate matrix contractions -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conjugate_density_product_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (G : E → Matrix ι ι ℂ)
    (hG : G = complexHessian a b u ∨ G = pureHessian a b u) :
    let H := fun y => (complexHessian a b u y).map star
    let C := fun y => (G y).map star
    matrixL a b u C x = contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) := by
  let H := fun y => (complexHessian a b u y).map star
  let C := fun y => (G y).map star
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu2 : ContDiffAt ℝ 2 u x := hu4.of_le (by norm_num)
  have hC (i j : ι) : ContDiffAt ℝ 2 (fun y => C y i j) x := by
    rcases hG with rfl | rfl
    · exact Complex.conjCLE.contDiff.contDiffAt.comp x (complexHessian_contDiffAt_two hu4 a b i j)
    · exact Complex.conjCLE.contDiff.contDiffAt.comp x (pureHessian_contDiffAt_two hu4 a b i j)
  have hH : H x = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu2 a b).apply j i
  have hi : (H x)⁻¹ = ((complexHessian a b u x)⁻¹).transpose := by
    rw [hH, Matrix.transpose_nonsing_inv]
  have he := linearized_conjugate_first_product_const hU hu a b hρ hdet hx G hG
  change contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a p) (b p) (matrixDZ (a q) (-b q) C) x) = _ at he
  have hc (p q : ι) := matrixDZ_mixed_comm_at (a p) (b p) (a q) (-b q) hC
  change matrixL a b u C x = contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x)
  simpa only [matrixL, hc, hi] using he

end PowerConvexity
