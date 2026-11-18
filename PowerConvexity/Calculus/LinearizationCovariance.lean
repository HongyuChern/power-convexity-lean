import PowerConvexity.Calculus.ComplexGradientMinimum
import PowerConvexity.Algebra.EigenvalueCovarianceTwo

/-! # Coordinate covariance of the actual elliptic contraction -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_congruence_quotient (Q H A : Matrix ι ι ℂ) (hQ : IsUnit Q.det) :
    ((Q*H*Q.conjTranspose)*(Q*A*Q.conjTranspose)⁻¹).trace = (H*A⁻¹).trace := by
  rw [congruence_quotient_similarity Q H A hQ,Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul Q hQ,Matrix.one_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_contraction_eq_trace {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : ι → E) (G : Matrix ι ι ℂ) :
    (∑ p,∑ q,G q p*dz (a q) (-b q) (dz (a p) (b p) (fun y => (f y:ℂ))) x) =
      (complexHessian a b f x*G).trace := by
  have hfc : ContDiffAt ℝ 2 (fun y => (f y:ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  simp_rw [dz_comm_at hfc (a _) (-b _) (a _) (b _)]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,complexHessian]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem complex_contraction_complexFrame {u f : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hf : ContDiffAt ℝ 2 f x)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) :
    (∑ p,∑ q,(complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ q p*
      dz (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
        (dz (complexFrameReal Q a b p) (complexFrameImag Q a b p) (fun y => (f y:ℂ))) x) =
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (f y:ℂ))) x) := by
  rw [complex_contraction_eq_trace hf,complex_contraction_eq_trace hf,
    complexHessian_complexFrame hu,complexHessian_complexFrame hf,
    trace_congruence_quotient Q _ _ hQ]

end PowerConvexity
