import PowerConvexity.Calculus.QuadraticSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Actual coordinate-dual quadratic tests after a complex frame change -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexFrameReal_complex_basis (Q : Matrix ι ι ℂ) (a : ι → E) (i : ι) :
    complexFrameReal Q a (fun j => Complex.I • a j) i = ∑ j, Q i j • a j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_smul,← add_smul]
  exact congrArg (fun z : ℂ => z • a j) (Complex.re_add_im (Q i j))

theorem complexFrameImag_eq_I_smul (Q : Matrix ι ι ℂ) (a : ι → E) (i : ι) :
    complexFrameImag Q a (fun j => Complex.I • a j) i =
      Complex.I • complexFrameReal Q a (fun j => Complex.I • a j) i := by
  rw [complexFrameReal_complex_basis,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,← sub_smul]
  apply congrArg (fun z : ℂ => z • a j)
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

noncomputable def complexFrameDual (e : Module.Basis ι ℂ E) (Q : Matrix ι ι ℂ) (i : ι) :
    E →L[ℂ] ℂ :=
  ∑ j, (Q⁻¹ j i) • LinearMap.toContinuousLinearMap (e.coord j)

theorem complexFrameDual_apply_basis (e : Module.Basis ι ℂ E) (Q : Matrix ι ι ℂ) (i j : ι) :
    complexFrameDual e Q i (e j) = Q⁻¹ j i := by
  simp [complexFrameDual,Module.Basis.coord_apply,Finsupp.single_apply,mul_ite,eq_comm]

theorem complexFrameDual_apply_frame (e : Module.Basis ι ℂ E) (Q : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) (i j : ι) :
    complexFrameDual e Q i (complexFrameReal Q e (fun k => Complex.I • e k) j) =
      if j=i then 1 else 0 := by
  rw [complexFrameReal_complex_basis,map_sum]
  simp only [map_smul,complexFrameDual_apply_basis,smul_eq_mul]
  change (Q*Q⁻¹) j i = _
  rw [Matrix.mul_nonsing_inv Q hQ]
  exact Matrix.one_apply

noncomputable def frameCoordinateSquare (e : Module.Basis ι ℂ E) (Q : Matrix ι ι ℂ)
    (i : ι) (x : E) : E → ℝ :=
  realPartSquare ((complexFrameDual e Q i).restrictScalars ℝ) x

theorem frameCoordinateSquare_pluriharmonic (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (i : ι) (x : E) :
    IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (frameCoordinateSquare e Q i x) := by
  apply realPartSquare_isPluriharmonicQuadratic
  intro j
  exact (complexFrameDual e Q i).map_smul Complex.I (e j)

theorem frameCoordinateSquare_center (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (i : ι) (x : E) : frameCoordinateSquare e Q i x x = 0 :=
  realPartSquare_center _ _

theorem frameCoordinateSquare_fderiv_center (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (i : ι) (x : E) :
    fderiv ℝ (frameCoordinateSquare e Q i x) x = 0 :=
  (realPartSquare_hasFDerivAt_center _ _).fderiv

theorem frameCoordinateSquare_mixed_zero (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (i : ι) (x y : E) :
    complexHessian (complexFrameReal Q e (fun j => Complex.I • e j))
      (complexFrameImag Q e (fun j => Complex.I • e j)) (frameCoordinateSquare e Q i x) y = 0 := by
  apply realPartSquare_mixedHessian_zero
  intro j
  rw [complexFrameImag_eq_I_smul]
  exact (complexFrameDual e Q i).map_smul Complex.I _

theorem frameCoordinateSquare_pure_diagonal (e : Module.Basis ι ℂ E)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (i : ι) (x y : E) :
    pureHessian (complexFrameReal Q e (fun j => Complex.I • e j))
      (complexFrameImag Q e (fun j => Complex.I • e j)) (frameCoordinateSquare e Q i x) y =
      Matrix.diagonal (fun j => if j=i then (1:ℂ) else 0) := by
  rw [frameCoordinateSquare,realPartSquare_pureHessian _ _ _ _ (fun j => ?_) y]
  · ext j k
    change complexFrameDual e Q i (complexFrameReal Q e (fun j => Complex.I • e j) j) *
      complexFrameDual e Q i (complexFrameReal Q e (fun j => Complex.I • e j) k) = _
    rw [complexFrameDual_apply_frame e Q hQ,complexFrameDual_apply_frame e Q hQ]
    simp only [Matrix.diagonal_apply]
    by_cases hji : j=i <;> by_cases hki : k=i <;> by_cases hjk : j=k <;> simp_all
  · rw [complexFrameImag_eq_I_smul]
    exact (complexFrameDual e Q i).map_smul Complex.I _

end PowerConvexity
