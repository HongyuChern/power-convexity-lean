import PowerConvexity.Calculus.ClassicalMinkowskiEndpointsTwo
import PowerConvexity.Calculus.HomotheticDirichletSandwichTwo

/-! # Quantitative actual ball trapping for zero-boundary CMA solutions.
This controls values on the entire ambient space after zero extension.
It supplies no Hessian or spectral-minimum lower bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadraticBallPotential_zeroExtension_eq_min {R : ℝ} (hR : 0 < R) (x : E) :
    (ball (0 : E) R).indicator (quadraticBallPotential 1 R) x = min (‖x‖^2-R^2) 0 := by
  classical
  by_cases hx : x ∈ ball (0 : E) R
  · rw [indicator_of_mem hx]
    have hn : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
    rw [min_eq_left (by nlinarith [norm_nonneg x] : ‖x‖^2-R^2 ≤ 0)]
    simp only [quadraticBallPotential,one_mul]
  · rw [indicator_of_notMem hx]
    have hn : R ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
    rw [min_eq_right (by nlinarith : 0 ≤ ‖x‖^2-R^2)]

theorem quadraticBallPotential_scaled_zeroExtension_eq_min
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (x : E) :
    c^2*(ball (0 : E) R).indicator (quadraticBallPotential 1 R) (c⁻¹ • x) =
      min (‖x‖^2-c^2*R^2) 0 := by
  rw [quadraticBallPotential_zeroExtension_eq_min hR,
    mul_min_of_nonneg _ _ (sq_nonneg c),mul_zero]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
  field_simp
  <;> ring

theorem ball_potential_clipped_value_difference {R c : ℝ}
    (hR : 0 < R) (hc : 0 < c) (x : E) :
    |c^2*(ball (0 : E) R).indicator (quadraticBallPotential 1 R) (c⁻¹ • x)-
      (ball (0 : E) R).indicator (quadraticBallPotential 1 R) x| ≤ |c^2-1| * R^2 := by
  rw [quadraticBallPotential_scaled_zeroExtension_eq_min hR hc,
    quadraticBallPotential_zeroExtension_eq_min hR]
  have hh := abs_min_sub_min_le_max (‖x‖^2-c^2*R^2) 0 (‖x‖^2-R^2) 0
  simp only [sub_self,abs_zero] at hh
  have he : (‖x‖^2-c^2*R^2)-(‖x‖^2-R^2) = -(c^2-1)*R^2 := by ring
  simpa only [he,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg R),
    max_eq_left (mul_nonneg (abs_nonneg (c^2-1)) (sq_nonneg R))] using hh

variable [ProperSpace E]

theorem classicalDirichlet_ball_trapping_uniform_C0_two
    {V : Set E} (hV : IsOpen V) (hVK : IsCompact (closure V))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {R lam : ℝ} (hR : 0 < R) (hlam : 1 ≤ lam)
    (hinner : dilatedDomain lam⁻¹ (ball (0 : E) R) ⊆ V)
    (houter : V ⊆ dilatedDomain lam (ball (0 : E) R))
    {v : E → ℝ} (hv : ClassicalDirichletDataTwo a b V v) :
    ∀ x : E, |V.indicator v x-(ball (0 : E) R).indicator (quadraticBallPotential 1 R) x| ≤
      (lam^2-1)*R^2 := by
  have hl : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hq := quadraticBallPotential_classical_data_two a b hab hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hs := homothetic_dirichlet_zeroExtension_sandwich_two isOpen_ball hV hBK hVK
    a b hab hq.continuous_closure hv.continuous_closure
    (hq.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) hq.2.2.1 hv.2.2.1
    hq.2.2.2.1 hv.2.2.2.1 hq.2.2.2.2 hv.2.2.2.2
    (inv_ne_zero hl.ne') hl.ne' hinner houter
  have hi : 0 < lam⁻¹ := inv_pos.mpr hl
  have hi1 : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam
  have hsq : 1 ≤ lam^2 := by nlinarith
  have hisq : lam⁻¹^2 ≤ 1 := by nlinarith
  have hcompare : 1-lam⁻¹^2 ≤ lam^2-1 := by
    have he : lam^2*(lam⁻¹)^2 = 1 := by field_simp
    nlinarith [sq_nonneg (lam^2-1),mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hisq)]
  intro x
  have hlow := (abs_le.mp (ball_potential_clipped_value_difference hR hl x)).1
  have hupp := (abs_le.mp (ball_potential_clipped_value_difference hR hi x)).2
  rw [abs_of_nonneg (sub_nonneg.mpr hsq)] at hlow
  rw [abs_of_nonpos (sub_nonpos.mpr hisq)] at hupp
  have hc := mul_le_mul_of_nonneg_right hcompare (sq_nonneg R)
  have hx := hs x
  apply abs_le.mpr
  constructor <;> linarith

end PowerConvexity
