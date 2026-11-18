import PowerConvexity.Calculus.PerturbationJets

/-! # Exact polynomial variation of the actual complex determinant in C2

The perturbation is an arbitrary actual C2 function, not an assumed Hessian
field. In complex dimension two the nonlinear remainder is exactly quadratic.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus

theorem determinant_two_affine_expansion
    (A H : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) :
    (A+s • H).det = A.det+s*(A.adjugate*H).trace+s^2*H.det := by
  simp only [Matrix.det_fin_two,Matrix.adjugate_fin_two,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem determinant_two_affine_hasDerivAt
    (A H : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun s : ℝ => (A+(s : ℂ) • H).det) (A.adjugate*H).trace 0 := by
  have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) 0 :=
    Complex.ofRealCLM.hasDerivAt
  have hp := (hasDerivAt_const (0 : ℝ) A.det).add
    (hs.mul_const (A.adjugate*H).trace)
  have hq := (hs.pow 2).mul_const H.det
  have he : (fun s : ℝ => (A+(s : ℂ) • H).det) =
      (fun s : ℝ => A.det+(s : ℂ)*(A.adjugate*H).trace+(s : ℂ)^2*H.det) :=
    funext (fun s => determinant_two_affine_expansion A H s)
  rw [he]
  simpa using! hp.add hq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexHessian_determinant_actual_potential_expansion_two
    (a b : Fin 2 → E) {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (s : ℝ) :
    (complexHessian a b (fun y => u y+s*h y) x).det =
      (complexHessian a b u x).det+
        (s : ℂ)*((complexHessian a b u x).adjugate*complexHessian a b h x).trace+
        (s : ℂ)^2*(complexHessian a b h x).det := by
  rw [complexHessian_add_at hu (contDiffAt_const.mul hh),
    complexHessian_const_mul_at hh]
  exact determinant_two_affine_expansion _ _ _

theorem complexHessian_determinant_actual_potential_hasDerivAt_two
    (a b : Fin 2 → E) {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) :
    HasDerivAt (fun s : ℝ => (complexHessian a b (fun y => u y+s*h y) x).det)
      ((complexHessian a b u x).adjugate*complexHessian a b h x).trace 0 := by
  have he : (fun s : ℝ => (complexHessian a b (fun y => u y+s*h y) x).det) =
      (fun s : ℝ => (complexHessian a b u x+(s : ℂ) • complexHessian a b h x).det) := by
    funext s
    rw [complexHessian_add_at hu (contDiffAt_const.mul hh),
      complexHessian_const_mul_at hh]
  rw [he]
  exact determinant_two_affine_hasDerivAt _ _

end PowerConvexity
