import PowerConvexity.Calculus.FrameDualQuadratics

/-! # The two concrete centered tests in Appendix A -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem exists_separation_test_quadratics_two (e : Module.Basis (Fin 2) ℂ E)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (x : E) :
    ∃ h g : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) h ∧
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) g ∧
      h x = 0 ∧ g x = 0 ∧ fderiv ℝ h x = 0 ∧ fderiv ℝ g x = 0 ∧
      complexHessian (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j)) h x = 0 ∧
      complexHessian (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j)) g x = 0 ∧
      pureHessian (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j)) h x =
          Matrix.diagonal (fun i => ((if i=0 then 1 else -1:ℝ):ℂ)) ∧
      pureHessian (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j)) g x =
          Matrix.diagonal (fun i => ((if i=0 then 1 else 0:ℝ):ℂ)) := by
  let q0 := frameCoordinateSquare e Q 0 x
  let q1 := frameCoordinateSquare e Q 1 x
  let h : E → ℝ := fun y => q0 y+(-1)*q1 y
  have hp0 := frameCoordinateSquare_pluriharmonic e Q 0 x
  have hp1 := frameCoordinateSquare_pluriharmonic e Q 1 x
  have hq0 := (IsQuadraticPolynomial_contDiff hp0.1 2).contDiffAt (x := x)
  have hq1 := (IsQuadraticPolynomial_contDiff hp1.1 2).contDiffAt (x := x)
  have hp : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) h :=
    IsPluriharmonicQuadratic_add hp0 (IsPluriharmonicQuadratic_const_mul hp1 (-1))
  refine ⟨h,q0,hp,hp0,?_,frameCoordinateSquare_center e Q 0 x,?_,
    frameCoordinateSquare_fderiv_center e Q 0 x,?_,
    frameCoordinateSquare_mixed_zero e Q 0 x x,?_,?_⟩
  · simp [h,q0,q1,frameCoordinateSquare_center]
  · change fderiv ℝ (fun y => q0 y+(-1)*q1 y) x = 0
    rw [fderiv_fun_add (hq0.differentiableAt (by norm_num))
      ((hq1.differentiableAt (by norm_num)).const_mul (-1)),
      fderiv_const_mul (hq1.differentiableAt (by norm_num))]
    simp [q0,q1,frameCoordinateSquare_fderiv_center]
  · change complexHessian _ _ (fun y => q0 y+(-1)*q1 y) x = 0
    rw [complexHessian_add_at hq0 (contDiffAt_const.mul hq1),
      complexHessian_const_mul_at hq1]
    simp [q0,q1,frameCoordinateSquare_mixed_zero]
  · change pureHessian _ _ (fun y => q0 y+(-1)*q1 y) x = _
    rw [pureHessian_add_at hq0 (contDiffAt_const.mul hq1),pureHessian_const_mul_at hq1]
    rw [frameCoordinateSquare_pure_diagonal e Q hQ,frameCoordinateSquare_pure_diagonal e Q hQ]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]
  · rw [show q0 = frameCoordinateSquare e Q 0 x from rfl,
      frameCoordinateSquare_pure_diagonal e Q hQ]
    congr 1
    funext i
    fin_cases i <;> norm_num

end PowerConvexity
