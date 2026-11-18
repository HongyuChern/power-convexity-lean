import PowerConvexity.Analysis.ActualScalarJetIterationStepTwo
import PowerConvexity.Calculus.ActualQuadraticImprovementTwo

/-! # The actual weighted polynomial update and its next residual.
All value, derivative and Hessian increments belong to the same function.
The next normalized residual is an exact function identity, not a choice
of a new representative of the original weak solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def scalarQuadraticUpdateTwo (q p : E → ℝ) (R a : ℝ) (x : E) : ℝ :=
  q x+a*scalarQuadraticLiftTwo R p x

def normalizedScalarResidualTwo (u q : E → ℝ) (R a : ℝ) (z : E) : ℝ :=
  a⁻¹*(R^2)⁻¹*(u (R • z)-q (R • z))

theorem scalarQuadraticUpdateTwo_isQuadratic {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (R a : ℝ) :
    IsQuadraticPolynomial (scalarQuadraticUpdateTwo q p R a) :=
  IsQuadraticPolynomial_add hq
    (IsQuadraticPolynomial_const_mul (scalarQuadraticLiftTwo_isQuadratic hp R) a)

theorem scalarQuadraticLiftTwo_fderiv_zero {R : ℝ} (hR : 0 < R) (p : E → ℝ) :
    fderiv ℝ (scalarQuadraticLiftTwo R p) 0 = R • fderiv ℝ p 0 := by
  have he : scalarQuadraticLiftTwo R p = fun x => R^2*p (R⁻¹ • x) :=
    funext (scalarQuadraticLiftTwo_apply hR.ne' p)
  rw [he]
  change fderiv ℝ (R^2 • (fun x => p (R⁻¹ • x))) 0 = _
  rw [fderiv_const_smul_field,Pi.smul_apply,fderiv_comp_smul,smul_zero,smul_smul]
  congr 1
  field_simp

theorem scalarQuadraticUpdateTwo_realHessian {q p : E → ℝ} {R a : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R) (x : E) :
    realHessian (scalarQuadraticUpdateTwo q p R a) x =
      realHessian q x+a • realHessian p (R⁻¹ • x) := by
  have hqc := (IsQuadraticPolynomial_contDiff hq 2).contDiffAt (x := x)
  have hpc := (IsQuadraticPolynomial_contDiff (scalarQuadraticLiftTwo_isQuadratic hp R) 2).contDiffAt (x := x)
  change realHessian (fun y => q y+a*scalarQuadraticLiftTwo R p y) x = _
  rw [realHessian_add hqc (contDiffAt_const.mul hpc),realHessian_const_mul,
    scalarQuadraticLiftTwo_realHessian hp hR]

theorem scalarQuadraticUpdateTwo_trace_zero {q p : E → ℝ} {R a : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R)
    (hqt : ∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0)
    (hpt : ∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) :
    ∀ x, (realBlockHessian realDirections imagDirections
      (scalarQuadraticUpdateTwo q p R a) x).trace = 0 := by
  intro x
  have he : realBlockHessian realDirections imagDirections (scalarQuadraticUpdateTwo q p R a) x =
      realBlockHessian realDirections imagDirections q x+
        a • realBlockHessian realDirections imagDirections p (R⁻¹ • x) := by
    ext i j
    simp only [realBlockHessian,scalarQuadraticUpdateTwo_realHessian hq hp hR,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,Pi.add_apply,
      _root_.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.smul_apply]
  rw [he,Matrix.trace_add,Matrix.trace_smul,hqt x,hpt _,smul_zero,add_zero]

theorem scalarQuadraticUpdateTwo_jet_increments {q p : E → ℝ} {R a : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R) :
    scalarQuadraticUpdateTwo q p R a 0-q 0 = a*R^2*p 0 ∧
    fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0-fderiv ℝ q 0 =
      (a*R) • fderiv ℝ p 0 ∧
    ∀ x, realHessian (scalarQuadraticUpdateTwo q p R a) x-realHessian q x =
      a • realHessian p 0 := by
  refine ⟨?_,?_,?_⟩
  · simp only [scalarQuadraticUpdateTwo,scalarQuadraticLiftTwo_apply hR.ne',smul_zero]
    ring
  · have hqd := (IsQuadraticPolynomial_contDiff hq 1).differentiable (by norm_num)
    have hpd := (IsQuadraticPolynomial_contDiff (scalarQuadraticLiftTwo_isQuadratic hp R) 1).differentiable (by norm_num)
    change fderiv ℝ (fun x => q x+(a • scalarQuadraticLiftTwo R p) x) 0-fderiv ℝ q 0 = _
    rw [fderiv_fun_add hqd.differentiableAt (hpd.const_smul a).differentiableAt,
      fderiv_const_smul_field,Pi.smul_apply,scalarQuadraticLiftTwo_fderiv_zero hR,
      smul_smul]
    ext v
    simp only [_root_.add_apply,_root_.sub_apply]
    ring
  · intro x
    rw [scalarQuadraticUpdateTwo_realHessian hq hp hR,
      quadratic_realHessian_from_jet_zero hp]
    ext v z
    simp only [_root_.add_apply,_root_.sub_apply]
    ring

theorem scalarQuadraticUpdateTwo_jet_increment_bounds {q p : E → ℝ} {R a M : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R)
    (ha : 0 ≤ a) (hp0 : |p 0| ≤ M) (hp1 : ‖fderiv ℝ p 0‖ ≤ M)
    (hp2 : ‖realHessian p 0‖ ≤ M) :
    |scalarQuadraticUpdateTwo q p R a 0-q 0| ≤ a*R^2*M ∧
    ‖fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0-fderiv ℝ q 0‖ ≤ a*R*M ∧
    ∀ x, ‖realHessian (scalarQuadraticUpdateTwo q p R a) x-realHessian q x‖ ≤ a*M := by
  obtain ⟨h0,h1,h2⟩ := scalarQuadraticUpdateTwo_jet_increments hq hp hR (a := a)
  refine ⟨?_,?_,?_⟩
  · rw [h0,abs_mul,abs_of_nonneg (mul_nonneg ha (sq_nonneg R))]
    exact mul_le_mul_of_nonneg_left hp0 (mul_nonneg ha (sq_nonneg R))
  · rw [h1,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ha hR.le)]
    exact mul_le_mul_of_nonneg_left hp1 (mul_nonneg ha hR.le)
  · intro x
    rw [h2 x,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hp2 ha

theorem normalizedScalarResidualTwo_update {u q p : E → ℝ} {R a r : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hr : 0 < r) :
    normalizedScalarResidualTwo u (scalarQuadraticUpdateTwo q p R a) (R*r) (a/2) =
      fun z => 2*(r^2)⁻¹*(normalizedScalarResidualTwo u q R a (r • z)-p (r • z)) := by
  funext z
  simp only [normalizedScalarResidualTwo,scalarQuadraticUpdateTwo,
    scalarQuadraticLiftTwo_apply hR.ne',smul_smul]
  rw [show R⁻¹*(R*r) = r from by field_simp]
  field_simp
  ring

end PowerConvexity
