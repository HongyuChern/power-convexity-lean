import PowerConvexity.Calculus.ClassicalComparisonTwo
import CHS.Calculus.PotentialConstants
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # The actual quadratic ball potential and its strict power convexity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def quadraticBallPotential (c R : ℝ) (y : E) : ℝ := c*(‖y‖^2-R^2)

theorem quadraticBallPotential_contDiff (c R : ℝ) (k : ℕ∞ω) :
    ContDiff ℝ k (quadraticBallPotential (E := E) c R) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)

theorem realHessian_norm_square (x v w : E) :
    realHessian (fun y : E => ‖y‖^2) x v w = 2*inner ℝ v w := by
  simpa only [ContinuousLinearMap.id_apply] using
    realHessian_norm_sq_comp (ContinuousLinearMap.id ℝ E) x v w

theorem quadraticBallPotential_realHessian (c R : ℝ) (x v w : E) :
    realHessian (quadraticBallPotential c R) x v w = 2*c*inner ℝ v w := by
  unfold quadraticBallPotential
  simp only [sub_eq_add_neg]
  rw [realHessian_const_mul,realHessian_add_const]
  simp only [smul_apply,smul_eq_mul,realHessian_norm_square]
  ring

theorem norm_square_complexHessian {ι : Type*} [DecidableEq ι]
    (a b : ι → E) (hab : Orthonormal ℝ (Sum.elim a b)) (x : E) :
    complexHessian a b (fun y : E => ‖y‖^2) x = 1 := by
  ext i j
  have h := orthonormal_iff_ite.mp hab
  have haa : inner ℝ (a i) (a j) = if i=j then 1 else 0 := by
    simpa using h (Sum.inl i) (Sum.inl j)
  have hbb : inner ℝ (b i) (b j) = if i=j then 1 else 0 := by
    simpa using h (Sum.inr i) (Sum.inr j)
  have hab' : inner ℝ (a i) (b j) = 0 := by simpa using h (Sum.inl i) (Sum.inr j)
  have hba : inner ℝ (b i) (a j) = 0 := by simpa using h (Sum.inr i) (Sum.inl j)
  rw [complexHessian_real_entry (contDiff_norm_sq ℝ).contDiffAt]
  simp only [realHessian_norm_square,haa,hbb,hab',hba]
  by_cases hij : i=j <;> norm_num [hij,Matrix.one_apply]

theorem quadraticBallPotential_complexHessian {ι : Type*} [DecidableEq ι]
    (a b : ι → E) (hab : Orthonormal ℝ (Sum.elim a b)) (c R : ℝ) (x : E) :
    complexHessian a b (quadraticBallPotential c R) x = (c:ℂ) • (1 : Matrix ι ι ℂ) := by
  unfold quadraticBallPotential
  rw [complexHessian_const_mul_at ((contDiff_norm_sq ℝ).sub contDiff_const).contDiffAt]
  simp only [sub_eq_add_neg]
  rw [complexHessian_add_const,norm_square_complexHessian a b hab]

theorem quadraticBallPotential_det_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b)) (c R : ℝ) (x : E) :
    (complexHessian a b (quadraticBallPotential c R) x).det = ((c^2:ℝ):ℂ) := by
  rw [quadraticBallPotential_complexHessian a b hab]
  simp [Matrix.det_smul]

theorem quadraticBallPotential_negative {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    {x : E} (hx : x ∈ ball 0 R) : quadraticBallPotential c R x < 0 := by
  have hxR : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
  have hs : ‖x‖^2 < R^2 := (sq_lt_sq₀ (norm_nonneg x) hR.le).mpr hxR
  exact mul_neg_of_pos_of_neg hc (sub_neg.mpr hs)

theorem quadraticBallPotential_boundary (c R : ℝ) {x : E} (hx : x ∈ sphere 0 R) :
    quadraticBallPotential c R x = 0 := by
  have hxR : ‖x‖ = R := by simpa only [mem_sphere,dist_zero_right] using hx
  simp [quadraticBallPotential,hxR]

theorem realHessian_powerTransform_pos_of_pos {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (hH : ∀ v : E, v ≠ 0 → 0 < realHessian u x v v) :
    ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  intro v hv
  rw [realHessian_powerTransform hu hx]
  apply mul_pos (sqrtSlope_pos hx)
  apply add_pos_of_pos_of_nonneg (hH v hv)
  exact div_nonneg (mul_self_nonneg _) (by linarith)

theorem quadraticBallPotential_powerHessian_pos {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    {x : E} (hx : x ∈ ball 0 R) :
    ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform (quadraticBallPotential c R)) x v v := by
  apply realHessian_powerTransform_pos_of_pos (quadraticBallPotential_contDiff c R 2).contDiffAt
    (quadraticBallPotential_negative hc hR hx)
  intro v hv
  rw [quadraticBallPotential_realHessian,real_inner_self_eq_norm_sq]
  exact mul_pos (mul_pos (by norm_num) hc) (sq_pos_of_pos (norm_pos_iff.mpr hv))

theorem quadraticBallPotential_strictConvexOn {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    StrictConvexOn ℝ (ball (0:E) R) (powerTransform (quadraticBallPotential c R)) := by
  apply strictConvexOn_of_realHessian_pos isOpen_ball (convex_ball 0 R)
    (powerTransform_contDiffOn (quadraticBallPotential_contDiff c R 2).contDiffOn
      (fun x hx => quadraticBallPotential_negative hc hR hx))
  exact fun x hx => quadraticBallPotential_powerHessian_pos hc hR hx

end PowerConvexity
