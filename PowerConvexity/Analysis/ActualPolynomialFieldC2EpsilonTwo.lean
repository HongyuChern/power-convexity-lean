import PowerConvexity.Analysis.ActualPolynomialFieldC2Two

/-! # Reconstructing C2 from epsilon-delta two-centre compatibility -/
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

theorem actual_C2_of_actual_jet_derivatives_two
    {U : Set E} (hU : IsOpen U) (f : E → ℝ)
    (D : E → E →L[ℝ] ℝ) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hfirst : ∀ x ∈ U, HasFDerivAt f (D x) x)
    (hsecond : ∀ x ∈ U, HasFDerivAt D (H x) x)
    (hHC : ContinuousOn H U) :
    ContDiffOn ℝ 2 f U ∧
      (∀ x ∈ U, fderiv ℝ f x = D x) ∧
      ∀ x ∈ U, realHessian f x = H x := by
  have hDC : ContDiffOn ℝ 1 D U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hU.uniqueDiffOn).mpr
    exact ⟨by norm_num,H,contDiffOn_zero.mpr hHC,
      fun x hx => (hsecond x hx).hasFDerivWithinAt⟩
  have hfC : ContDiffOn ℝ 2 f U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hU.uniqueDiffOn).mpr
    exact ⟨by norm_num,D,hDC,fun x hx => (hfirst x hx).hasFDerivWithinAt⟩
  refine ⟨hfC,fun x hx => (hfirst x hx).fderiv,?_⟩
  intro x hx
  have he : fderiv ℝ f =ᶠ[𝓝 x] D := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hfirst y hy).fderiv
  change fderiv ℝ (fderiv ℝ f) x = H x
  rw [he.fderiv_eq,(hsecond x hx).fderiv]

theorem actual_polynomial_field_C2_of_two_center_epsilon_two
    {U : Set E} (hU : IsOpen U) (P : E → E → ℝ)
    (hP : ∀ x ∈ U, IsQuadraticPolynomial (P x))
    (hmod : ∀ x ∈ U, ∀ epsilon > 0, ∃ delta > 0,
      ∀ y ∈ U, dist y x < delta →
        |P y y-P x y| ≤ epsilon*‖y-x‖^2 ∧
        ‖fderiv ℝ (P y) y-fderiv ℝ (P x) y‖ ≤ epsilon*‖y-x‖ ∧
        ‖realHessian (P y) y-realHessian (P x) x‖ ≤ epsilon) :
    ContDiffOn ℝ 2 (fun x => P x x) U ∧
      (∀ x ∈ U, fderiv ℝ (fun y => P y y) x = fderiv ℝ (P x) x) ∧
      ∀ x ∈ U, realHessian (fun y => P y y) x = realHessian (P x) x := by
  apply actual_C2_of_actual_jet_derivatives_two hU (fun x => P x x)
    (fun x => fderiv ℝ (P x) x) (fun x => realHessian (P x) x)
  · intro x hx
    obtain ⟨delta,hd,hb⟩ := hmod x hx 1 zero_lt_one
    let omega : E → ℝ := fun y => (1+‖realHessian (P x) x‖)*‖y-x‖
    have hc : ContinuousAt (fun y : E => ‖y-x‖) x := by fun_prop
    have hlim : Tendsto omega (𝓝 x) (𝓝 0) := by
      simpa only [omega,sub_self,norm_zero,mul_zero] using
        (tendsto_const_nhds.mul hc.tendsto :
          Tendsto (fun y : E => (1+‖realHessian (P x) x‖)*‖y-x‖) (𝓝 x)
            (𝓝 ((1+‖realHessian (P x) x‖)*‖x-x‖)))
    apply actual_hasFDerivAt_of_remainder_modulus_two hlim
    filter_upwards [hU.mem_nhds hx,Metric.ball_mem_nhds x hd] with y hyU hy
    have hv := (hb y hyU hy).1
    have he : P y y-P x x-fderiv ℝ (P x) x (y-x) =
        (P y y-P x y)+(P x y-P x x-fderiv ℝ (P x) x (y-x)) := by ring
    rw [Real.norm_eq_abs,he]
    calc
      _ ≤ |P y y-P x y|+|P x y-P x x-fderiv ℝ (P x) x (y-x)| := abs_add_le _ _
      _ ≤ 1*‖y-x‖^2+‖realHessian (P x) x‖*‖y-x‖^2 :=
        add_le_add hv (actual_quadratic_first_order_remainder_bound_two (hP x hx) x y)
      _ = omega y*‖y-x‖ := by dsimp [omega]; ring
  · intro x hx
    apply hasFDerivAt_iff_isLittleO.mpr
    apply Asymptotics.IsLittleO.of_bound
    intro epsilon hepsilon
    obtain ⟨delta,hd,hb⟩ := hmod x hx epsilon hepsilon
    filter_upwards [hU.mem_nhds hx,Metric.ball_mem_nhds x hd] with y hyU hy
    have hg := (hb y hyU hy).2.1
    rw [actual_quadratic_fderiv_from_jet_at_two (hP x hx) x y] at hg
    simpa only [sub_add_eq_sub_sub] using hg
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    obtain ⟨delta,hd,hb⟩ := hmod x hx (epsilon/2) (by positivity)
    filter_upwards [hU.mem_nhds hx,Metric.ball_mem_nhds x hd] with y hyU hy
    rw [dist_eq_norm]
    exact (hb y hyU hy).2.2.trans_lt (by linarith)

end PowerConvexity
