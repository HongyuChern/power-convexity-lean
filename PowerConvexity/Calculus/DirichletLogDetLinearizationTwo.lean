import PowerConvexity.Calculus.DeterminantPotentialVariationTwo
import PowerConvexity.Calculus.LinearizedDirichletC0Two
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The derivative of the actual log-determinant and its Dirichlet operator

This identifies the linear operator used in the C0 and kernel estimates with
the derivative of the nonlinear equation in every actual C2 direction.
It is a pointwise directional derivative, not yet a Banach-space inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem adjugate_trace_eq_det_inverse_trace_two
    (A H : Matrix (Fin 2) (Fin 2) ℂ) (hdet : A.det ≠ 0) :
    (A.adjugate*H).trace = A.det*(H*A⁻¹).trace := by
  have hadj : A.adjugate = A.det • A⁻¹ := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv,smul_smul,mul_inv_cancel₀ hdet,one_smul]
  rw [hadj,Matrix.smul_mul,Matrix.trace_smul,Matrix.trace_mul_comm]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_determinant_real_hasDerivAt_two
    (a b : Fin 2 → E) {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x)
    (hp : (complexHessian a b u x).PosDef) :
    HasDerivAt (fun s : ℝ => (complexHessian a b (fun y => u y+s*h y) x).det.re)
      ((complexHessian a b u x).det.re*linearizedCMAOperatorTwo a b u h x) 0 := by
  have hd := complexHessian_determinant_actual_potential_hasDerivAt_two a b hu hh
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have he : ((complexHessian a b u x).adjugate*complexHessian a b h x).trace.re =
      (complexHessian a b u x).det.re*linearizedCMAOperatorTwo a b u h x := by
    rw [adjugate_trace_eq_det_inverse_trace_two _ _ hp.det_pos.ne',Complex.mul_re]
    have him : (complexHessian a b u x).det.im = 0 :=
      (Complex.pos_iff.mp hp.det_pos).2.symm
    rw [him,zero_mul,sub_zero]
    congr 1
    unfold linearizedCMAOperatorTwo
    rw [← complexHessianContraction_pairing a b _ hh,complex_contraction_eq_trace hh]
  simpa only [Complex.reCLM_apply,he] using! hr

theorem actual_logdet_hasDerivAt_linearizedCMAOperatorTwo
    (a b : Fin 2 → E) {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x)
    (hp : (complexHessian a b u x).PosDef) :
    HasDerivAt (fun s : ℝ =>
      Real.log (complexHessian a b (fun y => u y+s*h y) x).det.re)
      (linearizedCMAOperatorTwo a b u h x) 0 := by
  have hd := actual_determinant_real_hasDerivAt_two a b hu hh hp
  have hp0 : (complexHessian a b u x).det.re ≠ 0 :=
    (Complex.pos_iff.mp hp.det_pos).1.ne'
  have he0 : (complexHessian a b (fun y => u y+(0 : ℝ)*h y) x).det.re =
      (complexHessian a b u x).det.re := by simp only [zero_mul,add_zero]
  have hlog := hd.log (by rw [he0]; exact hp0)
  simpa only [he0,mul_div_cancel_left₀ _ hp0] using! hlog

end PowerConvexity
