import PowerConvexity.Calculus.ModifiedContraction

/-! # Conjugation of actual elliptic contractions, with the p/q interchange -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contract_map_star_flip (W : Matrix ι ι ℂ) (hW : W.IsHermitian)
    (F : ι → ι → Matrix ι ι ℂ) :
    (contract W F).map star = contract W (fun p q => (F q p).map star) := by
  ext i j
  simp only [contract, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, star_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hW.apply q p]
  exact mul_comm _ _

theorem matrixDZ_mixed_map_star {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x)
    (a b c d : E) :
    matrixDZ c (-d) (matrixDZ a b (fun y => (G y).map star)) x =
      (matrixDZ a (-b) (matrixDZ c d G) x).map star := by
  have he : matrixDZ a b (fun y => (G y).map star) =
      fun y => (matrixDZ a (-b) G y).map star := funext fun y => matrixDZ_map_star a b G y
  rw [he, matrixDZ_map_star, neg_neg,
    matrixDZ_mixed_comm_at c d a (-b) hG]

theorem matrixL_map_star {u : E → ℝ} {G : E → Matrix ι ι ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x)
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x) (a b : ι → E) :
    matrixL a b u (fun y => (G y).map star) x = (matrixL a b u G x).map star := by
  unfold matrixL
  rw [contract_map_star_flip _ (complexHessian_isHermitian hu a b).inv]
  simp only [matrixDZ_mixed_map_star hG]

theorem matrix_map_star_add (A B : Matrix ι ι ℂ) :
    (A+B).map star = A.map star + B.map star := by
  ext i j
  exact star_add _ _

theorem modifiedA_conjugate_contracted_second {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ) :
    matrixL a b u (fun y => (modifiedA a b u y).map star) x =
      matrixL a b u (fun y => (complexHessian a b u y).map star) x +
        contract (complexHessian a b u x)⁻¹ (fun p q =>
          (modificationASecond (powerWeight (u x)) (complexGradient a b u x)
            (modifiedA a b u x) (modifiedB a b u x) q p).map star) := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  rw [matrixL_map_star hu2 (modifiedA_contDiffAt_two hu hx a b),
    modifiedA_contracted_second hu hx a b hdet, matrix_map_star_add,
    ← matrixL_map_star hu2 (complexHessian_contDiffAt_two hu a b),
    contract_map_star_flip _ (complexHessian_isHermitian hu2 a b).inv]

theorem modifiedB_conjugate_contracted_second {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ) :
    matrixL a b u (fun y => (modifiedB a b u y).map star) x =
      matrixL a b u (fun y => (pureHessian a b u y).map star) x +
        contract (complexHessian a b u x)⁻¹ (fun p q =>
          (modificationBSecond (powerWeight (u x)) (complexGradient a b u x)
            (modifiedA a b u x) (modifiedB a b u x) q p).map star) := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  rw [matrixL_map_star hu2 (modifiedB_contDiffAt_two hu hx a b),
    modifiedB_contracted_second hu hx a b hdet, matrix_map_star_add,
    ← matrixL_map_star hu2 (pureHessian_contDiffAt_two hu a b),
    contract_map_star_flip _ (complexHessian_isHermitian hu2 a b).inv]

end PowerConvexity
