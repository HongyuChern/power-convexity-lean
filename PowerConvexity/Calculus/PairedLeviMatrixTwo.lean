import PowerConvexity.Calculus.FrameDualQuadratics

/-! # Positive paired real Hessians give the actual strict psh matrix -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Matrix
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem complexHessian_posDef_of_paired_positive_two
    (e : Module.Basis (Fin 2) ℂ E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hp : ∀ v : E, v ≠ 0 →
      0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v)) :
    (complexHessian e (fun j => Complex.I • e j) f x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (complexHessian_isHermitian hf _ _)
  intro z hz
  let Q : Matrix (Fin 2) (Fin 2) ℂ := fun _ j => star (z j)
  let v : E := e.equivFun.symm (star z)
  have hv : v ≠ 0 := by
    intro hv0
    have hs : star z = 0 := e.equivFun.symm.injective (by simpa only [map_zero] using hv0)
    exact hz (star_eq_zero.mp hs)
  have hform : (Q * complexHessian e (fun j => Complex.I • e j) f x * Q.conjTranspose) 0 0 =
      star z ⬝ᵥ (complexHessian e (fun j => Complex.I • e j) f x).mulVec z := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Q,star_star,star_apply,
      dotProduct,Matrix.mulVec,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    rfl
  have hvframe : complexFrameReal Q e (fun j => Complex.I • e j) 0 = v := by
    rw [complexFrameReal_complex_basis]
    exact (e.equivFun_symm_apply (star z)).symm
  have hIframe : complexFrameImag Q e (fun j => Complex.I • e j) 0 = Complex.I • v := by
    rw [complexFrameImag_eq_I_smul,hvframe]
  rw [← hform,← complexHessian_complexFrame hf]
  have he : complexHessian (complexFrameReal Q e (fun j => Complex.I • e j))
      (complexFrameImag Q e (fun j => Complex.I • e j)) f x 0 0 =
      (((realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v))/4 : ℝ) : ℂ) := by
    rw [complexHessian_real_entry hf,hvframe,hIframe,realHessian_symm hf v (Complex.I • v)]
    push_cast
    ring
  rw [he]
  exact Complex.pos_iff.mpr ⟨by simpa using (div_pos (hp v hv) (by norm_num : (0 : ℝ) < 4)),by simp⟩

end PowerConvexity
