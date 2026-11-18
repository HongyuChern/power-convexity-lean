import PowerConvexity.Calculus.ActualQuadraticResidualTwo

/-! # Actual polynomial update after one residual improvement.
The same radius R and same polynomial p are used in the function identity,
Hessian control, changed background and closed-ball error.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def scalarQuadraticLiftTwo (R : ℝ) (p : E → ℝ) : E → ℝ :=
  complexScaledPullbackTwo 1 R⁻¹ p

theorem scalarQuadraticLiftTwo_apply {R : ℝ} (hR : R ≠ 0) (p : E → ℝ) (x : E) :
    scalarQuadraticLiftTwo R p x = R^2*p (R⁻¹ • x) := by
  simp only [scalarQuadraticLiftTwo,complexScaledPullbackTwo,complexMatrixRealMap_one,inv_pow,inv_inv]

theorem scalarQuadraticLiftTwo_isQuadratic {p : E → ℝ}
    (hp : IsQuadraticPolynomial p) (R : ℝ) : IsQuadraticPolynomial (scalarQuadraticLiftTwo R p) :=
  complexScaledPullbackTwo_isQuadratic hp _ _

theorem scalarQuadraticLiftTwo_realHessian {p : E → ℝ} {R : ℝ}
    (hp : IsQuadraticPolynomial p) (hR : 0 < R) (x : E) :
    realHessian (scalarQuadraticLiftTwo R p) x = realHessian p (R⁻¹ • x) := by
  have hpc := IsQuadraticPolynomial_contDiff hp 2
  ext v z
  exact (complexScaledPullbackTwo_realHessian (G := 1) (inv_pos.mpr hR) hpc.contDiffAt v z).trans
    (by simp only [complexMatrixRealMap_one])

theorem scalarQuadraticLiftTwo_complexHessian {p : E → ℝ} {R : ℝ}
    (hp : IsQuadraticPolynomial p) (hR : 0 < R) (x : E) :
    complexHessian realDirections imagDirections (scalarQuadraticLiftTwo R p) x =
      complexHessian realDirections imagDirections p (R⁻¹ • x) := by
  have hpc := IsQuadraticPolynomial_contDiff hp 2
  change complexHessian realDirections imagDirections (complexScaledPullbackTwo 1 R⁻¹ p) x = _
  rw [complexScaledPullbackTwo_complexHessian (inv_pos.mpr hR) hpc.contDiffAt]
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℂ).map star = 1 := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ).transpose.conjTranspose = 1
    simp only [Matrix.transpose_one,Matrix.conjTranspose_one]
  simp only [Matrix.transpose_one,hI,Matrix.one_mul,Matrix.mul_one,complexMatrixRealMap_one]

def quadraticImprovementTwo (q p : E → ℝ) (R : ℝ) (x : E) : ℝ :=
  q x+scalarQuadraticLiftTwo R p x

theorem quadraticImprovementTwo_isQuadratic {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (R : ℝ) :
    IsQuadraticPolynomial (quadraticImprovementTwo q p R) :=
  IsQuadraticPolynomial_add hq (scalarQuadraticLiftTwo_isQuadratic hp R)

theorem quadraticImprovementTwo_complexHessian {q p : E → ℝ} {R : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R) (x : E) :
    1+complexHessian realDirections imagDirections (quadraticImprovementTwo q p R) x =
      (1+complexHessian realDirections imagDirections q 0)+
        complexHessian realDirections imagDirections p (R⁻¹ • x) := by
  have hqc := IsQuadraticPolynomial_contDiff hq 2
  have hlc := IsQuadraticPolynomial_contDiff (scalarQuadraticLiftTwo_isQuadratic hp R) 2
  change 1+complexHessian realDirections imagDirections (fun y => q y+scalarQuadraticLiftTwo R p y) x = _
  rw [complexHessian_add_at hqc.contDiffAt hlc.contDiffAt,
    quadratic_complexHessian_from_zero_two hq,scalarQuadraticLiftTwo_complexHessian hp hR,add_assoc]

theorem quadraticImprovementTwo_realHessian_norm {q p : E → ℝ} {R K D : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R)
    (hqH : ∀ x, ‖realHessian q x‖ ≤ K) (hpH : ∀ x, ‖realHessian p x‖ ≤ D) (x : E) :
    ‖realHessian (quadraticImprovementTwo q p R) x‖ ≤ K+D := by
  have hqc := IsQuadraticPolynomial_contDiff hq 2
  have hlc := IsQuadraticPolynomial_contDiff (scalarQuadraticLiftTwo_isQuadratic hp R) 2
  change ‖realHessian (fun y => q y+scalarQuadraticLiftTwo R p y) x‖ ≤ K+D
  rw [realHessian_add hqc.contDiffAt hlc.contDiffAt,scalarQuadraticLiftTwo_realHessian hp hR]
  exact (norm_add_le (realHessian q x) (realHessian p (R⁻¹ • x))).trans (add_le_add (hqH x) (hpH _))

theorem quadraticImprovementTwo_value_error {w q p : E → ℝ} {R r ε θ : ℝ}
    (hR : 0 < R)
    (hb : ∀ y ∈ closedBall (0 : E) r, |quadraticResidualTwo w q R y-p y| ≤ θ*ε*r^2) :
    ∀ x ∈ closedBall (0 : E) (R*r), |w x-quadraticImprovementTwo q p R x| ≤ θ*ε*(R*r)^2 := by
  intro x hx
  have hxn : ‖x‖ ≤ R*r := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hy : R⁻¹ • x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (mul_le_mul_of_nonneg_left hxn (inv_pos.mpr hR).le).trans_eq (by field_simp)
  have he : w x-quadraticImprovementTwo q p R x =
      R^2*(quadraticResidualTwo w q R (R⁻¹ • x)-p (R⁻¹ • x)) := by
    rw [quadraticImprovementTwo,scalarQuadraticLiftTwo_apply hR.ne',quadraticResidualTwo_apply,
      smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos (sq_pos_of_pos hR)]
  exact (mul_le_mul_of_nonneg_left (hb _ hy) (sq_nonneg R)).trans_eq (by ring)

end PowerConvexity
