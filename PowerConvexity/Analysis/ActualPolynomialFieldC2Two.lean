import PowerConvexity.Analysis.ActualCompatibleJetReconstructionTwo

/-! # Actual C2 reconstruction from a compatible quadratic field

The value of the representative at x is the value of the approximating
polynomial at x. The proof identifies both derivatives from two-centre jet
moduli. Equality almost everywhere with a weak solution is a separate step.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_bilinear_diagonal_norm_bound_two
    (H : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : |H v v| ≤ ‖H‖*‖v‖^2 := by
  calc
    |H v v| = ‖H v v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖H v‖*‖v‖ := (H v).le_opNorm v
    _ ≤ (‖H‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg v)
    _ = _ := by ring

theorem actual_quadratic_first_order_remainder_bound_two {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (x y : E) :
    |q y-q x-fderiv ℝ q x (y-x)| ≤ ‖realHessian q x‖*‖y-x‖^2 := by
  have he : q y-q x-fderiv ℝ q x (y-x) = (1/2 : ℝ)*realHessian q x (y-x) (y-x) := by
    rw [quadratic_exact_Taylor hq x y]
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  exact (mul_le_mul_of_nonneg_left
    (actual_bilinear_diagonal_norm_bound_two (realHessian q x) (y-x)) (by norm_num)).trans
      (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (by norm_num))

theorem actual_polynomial_field_C2_of_two_center_moduli_two
    {U : Set E} (hU : IsOpen U) (P : E → E → ℝ)
    (hP : ∀ x ∈ U, IsQuadraticPolynomial (P x))
    (hmod : ∀ x ∈ U, ∃ omega : E → ℝ, Tendsto omega (𝓝 x) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 x, y ∈ U →
        |P y y-P x y| ≤ omega y*‖y-x‖^2 ∧
        ‖fderiv ℝ (P y) y-fderiv ℝ (P x) y‖ ≤ omega y*‖y-x‖ ∧
        ‖realHessian (P y) y-realHessian (P x) x‖ ≤ omega y) :
    ContDiffOn ℝ 2 (fun x => P x x) U ∧
      (∀ x ∈ U, fderiv ℝ (fun y => P y y) x = fderiv ℝ (P x) x) ∧
      ∀ x ∈ U, realHessian (fun y => P y y) x = realHessian (P x) x := by
  apply actual_C2_of_compatible_jet_moduli_two hU (fun x => P x x)
    (fun x => fderiv ℝ (P x) x) (fun x => realHessian (P x) x)
  intro x hx
  obtain ⟨omega,hlim,hb⟩ := hmod x hx
  let eta : E → ℝ := fun y => (omega y+‖realHessian (P x) x‖)*‖y-x‖
  have hnorm : Tendsto (fun y : E => ‖y-x‖) (𝓝 x) (𝓝 0) := by
    have hc : ContinuousAt (fun y : E => ‖y-x‖) x := by fun_prop
    simpa only [sub_self,norm_zero] using hc.tendsto
  have heta : Tendsto eta (𝓝 x) (𝓝 0) := by
    simpa only [zero_add,mul_zero] using (hlim.add_const ‖realHessian (P x) x‖).mul hnorm
  refine ⟨eta,omega,omega,heta,hlim,hlim,?_⟩
  filter_upwards [hb] with y hy hyU
  obtain ⟨hval,hgrad,hH⟩ := hy hyU
  refine ⟨?_,?_,hH⟩
  · have he : P y y-P x x-fderiv ℝ (P x) x (y-x) =
        (P y y-P x y)+(P x y-P x x-fderiv ℝ (P x) x (y-x)) := by ring
    rw [Real.norm_eq_abs,he]
    calc
      _ ≤ |P y y-P x y|+|P x y-P x x-fderiv ℝ (P x) x (y-x)| := abs_add_le _ _
      _ ≤ omega y*‖y-x‖^2+‖realHessian (P x) x‖*‖y-x‖^2 :=
        add_le_add hval (actual_quadratic_first_order_remainder_bound_two (hP x hx) x y)
      _ = eta y*‖y-x‖ := by dsimp [eta]; ring
  · rw [actual_quadratic_fderiv_from_jet_at_two (hP x hx) x y] at hgrad
    simpa only [sub_add_eq_sub_sub] using hgrad

end PowerConvexity
