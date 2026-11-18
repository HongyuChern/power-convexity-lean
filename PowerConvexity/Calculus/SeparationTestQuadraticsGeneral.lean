import PowerConvexity.Calculus.FrameDualQuadratics

/-! # Centered opposite diagonal tests in arbitrary complex dimension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_separation_test_quadratic (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (x : E) (i j : ι) :
    ∃ h : E → ℝ,
      IsPluriharmonicQuadratic e (fun k => Complex.I • e k) h ∧
      h x = 0 ∧ fderiv ℝ h x = 0 ∧
      complexHessian (complexFrameReal Q e (fun k => Complex.I • e k))
        (complexFrameImag Q e (fun k => Complex.I • e k)) h x = 0 ∧
      pureHessian (complexFrameReal Q e (fun k => Complex.I • e k))
        (complexFrameImag Q e (fun k => Complex.I • e k)) h x =
        Matrix.diagonal (fun k => (((if k=i then 1 else 0)-(if k=j then 1 else 0):ℝ):ℂ)) := by
  let q0 := frameCoordinateSquare e Q i x
  let q1 := frameCoordinateSquare e Q j x
  let h : E → ℝ := fun y => q0 y+(-1)*q1 y
  have hp0 := frameCoordinateSquare_pluriharmonic e Q i x
  have hp1 := frameCoordinateSquare_pluriharmonic e Q j x
  have hq0 := (IsQuadraticPolynomial_contDiff hp0.1 2).contDiffAt (x := x)
  have hq1 := (IsQuadraticPolynomial_contDiff hp1.1 2).contDiffAt (x := x)
  refine ⟨h,IsPluriharmonicQuadratic_add hp0 (IsPluriharmonicQuadratic_const_mul hp1 (-1)),?_,?_,?_,?_⟩
  · simp [h,q0,q1,frameCoordinateSquare_center]
  · change fderiv ℝ (fun y => q0 y+(-1)*q1 y) x = 0
    rw [fderiv_fun_add (hq0.differentiableAt (by norm_num))
      ((hq1.differentiableAt (by norm_num)).const_mul (-1)),
      fderiv_const_mul (hq1.differentiableAt (by norm_num))]
    simp [q0,q1,frameCoordinateSquare_fderiv_center]
  · change complexHessian _ _ (fun y => q0 y+(-1)*q1 y) x = 0
    rw [complexHessian_add_at hq0 (contDiffAt_const.mul hq1),complexHessian_const_mul_at hq1]
    simp [q0,q1,frameCoordinateSquare_mixed_zero]
  · change pureHessian _ _ (fun y => q0 y+(-1)*q1 y) x = _
    rw [pureHessian_add_at hq0 (contDiffAt_const.mul hq1),pureHessian_const_mul_at hq1]
    rw [frameCoordinateSquare_pure_diagonal e Q hQ,frameCoordinateSquare_pure_diagonal e Q hQ]
    ext k l
    by_cases hkl : k=l
    · subst l
      simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,smul_eq_mul]
      split_ifs <;> norm_num
    · simp [Matrix.diagonal_apply,hkl]

end PowerConvexity
