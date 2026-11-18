import PowerConvexity.Calculus.FrameDualQuadratics

/-! # Actual strict psh matrices give positive paired real Hessians -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Matrix
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem complexHessian_posDef_paired_positive_two
    (e : Module.Basis (Fin 2) ℂ E) {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hpos : (complexHessian e (fun j => Complex.I • e j) f x).PosDef)
    (v : E) (hv : v ≠ 0) :
    0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v) := by
  let z : Fin 2 → ℂ := fun j => e.repr v j
  let Q : Matrix (Fin 2) (Fin 2) ℂ := fun _ j => z j
  have hz : z ≠ 0 := by
    intro he
    apply hv
    have hs := e.sum_repr v
    have hzj (j : Fin 2) : e.repr v j = 0 := congrFun he j
    simpa only [hzj,zero_smul,Finset.sum_const_zero] using hs.symm
  have hstar : star z ≠ 0 := by simpa only [star_ne_zero] using hz
  have hp := hpos.dotProduct_mulVec_pos hstar
  have hform : (Q * complexHessian e (fun j => Complex.I • e j) f x * Q.conjTranspose) 0 0 =
      star (star z) ⬝ᵥ (complexHessian e (fun j => Complex.I • e j) f x).mulVec (star z) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Q,star_star,star_apply,
      dotProduct,Matrix.mulVec,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    rfl
  have hvframe : complexFrameReal Q e (fun j => Complex.I • e j) 0 = v := by
    rw [complexFrameReal_complex_basis]
    exact e.sum_repr v
  have hIframe : complexFrameImag Q e (fun j => Complex.I • e j) 0 = Complex.I • v := by
    rw [complexFrameImag_eq_I_smul,hvframe]
  rw [← hform,← complexHessian_complexFrame hf,
    complexHessian_real_entry hf,hvframe,hIframe] at hp
  have hr := (Complex.pos_iff.mp hp).1
  norm_num [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.mul_im] at hr
  linarith

end PowerConvexity
