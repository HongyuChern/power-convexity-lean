import PowerConvexity.Analysis.ActualUniformQuotientDerivativeInterpolationFour

/-! # Quantitative derivative decay from the actual quotient power remainder

Choosing the finite-difference length d*d^(alpha/(1+beta))/2 gives a genuine
common derivative modulus of exponent alpha*beta/(1+beta).
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_derivative_power_interpolation_four
    {u : V → ℝ} {c : V} {L : V →L[ℝ] ℝ} {k C H alpha beta d : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (ha : 0 < alpha) (hb : 0 < beta)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hu : ∀ x ∈ ball c d, DifferentiableAt ℝ u x)
    (hvalue : ∀ x ∈ ball c d, |u x-(k+L (x-c))| ≤ C*d*d^alpha)
    (hmod : ∀ x ∈ ball c d,
      ‖fderiv ℝ u x-fderiv ℝ u c‖ ≤ H*(‖x-c‖/d)^beta) :
    ‖fderiv ℝ u c-L‖ ≤ (4*C+H)*d^(alpha*beta/(1+beta)) := by
  let t := alpha/(1+beta)
  let gamma := alpha*beta/(1+beta)
  have hden : 0 < 1+beta := by linarith
  have ht : 0 < t := div_pos ha hden
  have hp : 0 < d^t := Real.rpow_pos_of_pos hd t
  have hp1 : d^t ≤ 1 := Real.rpow_le_one hd.le hd1 ht.le
  let h := (d/2)*d^t
  have hh : 0 < h := mul_pos (half_pos hd) hp
  have hhd : h < d := by dsimp only [h]; nlinarith
  have hE : 0 ≤ C*d*d^alpha := by positivity
  have he := actual_derivative_from_holder_affine_remainder_four hE hH hb.le hh hhd hu hvalue hmod
  have halpha : alpha=t+gamma := by dsimp only [t,gamma]; field_simp
  have hgamma : t*beta=gamma := by dsimp only [t,gamma]; ring
  have hpow : d^alpha=d^t*d^gamma := by rw [halpha,Real.rpow_add hd]
  have hvalueTerm : 2*(C*d*d^alpha)/h=4*C*d^gamma := by
    rw [hpow]
    dsimp only [h]
    field_simp
    <;> ring
  have hratio : h/d ≤ d^t := by
    apply (div_le_iff₀ hd).2
    dsimp only [h]
    nlinarith
  have hpower : (h/d)^beta ≤ d^gamma := by
    have hm := Real.rpow_le_rpow (div_nonneg hh.le hd.le) hratio hb.le
    rw [← Real.rpow_mul hd.le,hgamma] at hm
    exact hm
  rw [hvalueTerm] at he
  calc
    _ ≤ 4*C*d^gamma+H*d^gamma :=
      he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower hH))
    _ = _ := by dsimp only [gamma]; ring

theorem actual_quotient_interpolation_exponent_positive_four
    {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    0 < alpha*beta/(1+beta) ∧ alpha*beta/(1+beta) < alpha := by
  have hd : 0 < 1+beta := by linarith
  refine ⟨div_pos (mul_pos ha hb) hd,?_⟩
  apply (div_lt_iff₀ hd).2
  nlinarith

end PowerConvexity
