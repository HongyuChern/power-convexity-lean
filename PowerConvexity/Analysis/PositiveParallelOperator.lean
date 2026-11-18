import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! # Quantitative positive operator bounds on an actual tangent subspace.
Zero eigenvalues are permitted. The comparison does not assume strict real
curvature and will be applied to the derivative of the actual unit normal.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped RealInnerProductSpace
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem positive_tangent_operator_square_le
    (S : E →L[ℝ] E) (T : Submodule ℝ E)
    (hT : ∀ v ∈ T, S v ∈ T)
    (hsym : ∀ v ∈ T, ∀ w ∈ T, inner ℝ (S v) w = inner ℝ (S w) v)
    (hpos : ∀ v ∈ T, 0 ≤ inner ℝ (S v) v)
    {M : ℝ} (hM : 0 < M)
    (hupper : ∀ v ∈ T, inner ℝ (S v) v ≤ M*‖v‖^2)
    {w : E} (hw : w ∈ T) :
    ‖S w‖^2 ≤ M*inner ℝ (S w) w := by
  have hz := hT w hw
  have hh := hpos (M • w-S w) (T.sub_mem (T.smul_mem M hw) hz)
  have hc : inner ℝ (S (S w)) w = ‖S w‖^2 := by
    rw [hsym (S w) hz w hw,real_inner_self_eq_norm_sq]
  simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,hc] at hh
  have hu := hupper (S w) hz
  apply (mul_le_mul_iff_right₀ hM).mp
  nlinarith only [hh,hu]

theorem parallel_positive_operator_form_lower
    (S : E →L[ℝ] E) (T : Submodule ℝ E)
    (hT : ∀ v ∈ T, S v ∈ T)
    (hsym : ∀ v ∈ T, ∀ w ∈ T, inner ℝ (S v) w = inner ℝ (S w) v)
    (hpos : ∀ v ∈ T, 0 ≤ inner ℝ (S v) v)
    {M : ℝ} (hM : 0 < M)
    (hupper : ∀ v ∈ T, inner ℝ (S v) v ≤ M*‖v‖^2)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hR : 0 ≤ R)
    {w : E} (hw : w ∈ T) :
    inner ℝ (S (t • w+((1-t)*R) • S w)) (t • w+((1-t)*R) • S w) /
        (1+R*M) ≤ inner ℝ (S w) (t • w+((1-t)*R) • S w) := by
  let r := (1-t)*R
  have hr : 0 ≤ r := mul_nonneg (sub_nonneg.mpr ht1) hR
  have hz := hT w hw
  have hsquare := positive_tangent_operator_square_le S T hT hsym hpos hM hupper hw
  have hzupper := hupper (S w) hz
  have hq := hpos w hw
  have hc : inner ℝ (S (S w)) w = ‖S w‖^2 := by
    rw [hsym (S w) hz w hw,real_inner_self_eq_norm_sq]
  have hexpand :
      inner ℝ (S (t • w+r • S w)) (t • w+r • S w) =
        t^2*inner ℝ (S w) w+2*t*r*‖S w‖^2+r^2*inner ℝ (S (S w)) (S w) := by
    simp only [map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,hc]
    ring
  have hnew : inner ℝ (S w) (t • w+r • S w) = t*inner ℝ (S w) w+r*‖S w‖^2 := by
    simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hn : 0 ≤ inner ℝ (S w) (t • w+r • S w) := by
    rw [hnew]
    positivity
  have hstep : inner ℝ (S (t • w+r • S w)) (t • w+r • S w) ≤
      (t+r*M)*inner ℝ (S w) (t • w+r • S w) := by
    rw [hexpand,hnew]
    have h1 := mul_nonneg (mul_nonneg ht hr) (sub_nonneg.mpr hsquare)
    have h2 := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hzupper)
    nlinarith only [h1,h2]
  have hden : 0 < 1+R*M := by positivity
  apply (div_le_iff₀ hden).mpr
  have hfactor : t+r*M ≤ 1+R*M := by
    dsimp only [r]
    nlinarith only [ht1,mul_nonneg ht (mul_nonneg hR hM.le)]
  exact hstep.trans (by nlinarith only [mul_le_mul_of_nonneg_right hfactor hn])

end PowerConvexity
