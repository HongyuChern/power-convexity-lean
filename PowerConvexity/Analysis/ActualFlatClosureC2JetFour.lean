import PowerConvexity.Analysis.ActualFlatJetExtensionFour
import CHS.Calculus.ClosureRegularity

/-! # The actual closure C2 jet on a smaller flat half-ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatClosureC2JetFour {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha Ka Kf F B R gamma M T beta H C : ℝ}
    (hR : 0 < R) (hgamma : 0 < gamma) (hbeta : 0 < beta)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (J : ActualFlatFullJetControlFour D R gamma M T beta H C) :
    ClosureC2Jet D.solution (actualFlatUpperBallFour N (1/8 : ℝ)) := by
  let g := fun c : E => fderiv ℝ (J.polynomial c) c
  let h := fun c : E => realHessian (J.polynomial c) c
  have hg : ContinuousOn g (actualFlatBoundaryDiskFour N) :=
    actual_local_holder_continuousOn_four (by positivity : 0 < R/8) (by norm_num : (0 : ℝ) < 1)
      (fun x hx y hy hnear => by simpa only [Real.rpow_one] using J.gradient_compatibility x hx y hy hnear)
  have hh : ContinuousOn h (actualFlatBoundaryDiskFour N) :=
    actual_local_holder_continuousOn_four (by positivity : 0 < R/4) hbeta J.hessian_compatibility
  have hsub : actualFlatUpperBallFour N (1/4 : ℝ) ⊆ actualFlatUpperBallFour N 1 :=
    fun x hx => ⟨ball_subset_ball (by norm_num) hx.1,hx.2⟩
  have hd : ContDiffOn ℝ 1 (fderiv ℝ D.solution) (actualFlatUpperBallFour N 1) :=
    D.solution_regular.fderiv_of_isOpen (actualFlatUpperBallFour_isOpen N 1) (by norm_num)
  have hDc : ContinuousOn (fderiv ℝ D.solution) (actualFlatUpperBallFour N (1/4 : ℝ)) :=
    hd.continuousOn.mono hsub
  have hHc : ContinuousOn (realHessian D.solution) (actualFlatUpperBallFour N (1/4 : ℝ)) :=
    (hd.continuousOn_fderiv_of_isOpen (actualFlatUpperBallFour_isOpen N 1) (by norm_num)).mono hsub
  have hgrad : ContinuousOn (actualFlatJetExtensionFour N (fderiv ℝ D.solution) g)
      (actualFlatClosedUpperBallFour N (1/8 : ℝ)) := by
    apply actual_flat_jet_extension_continuous_four hN hDc hg (by positivity : 0 < R/3)
      (w := fun s : ℝ => (C+4*T)*(s/4)) (by fun_prop) (by ring)
    intro x hx hnear
    exact (J.interior_error x hx (by linarith)).1
  have hhess : ContinuousOn (actualFlatJetExtensionFour N (realHessian D.solution) h)
      (actualFlatClosedUpperBallFour N (1/8 : ℝ)) := by
    have hw : Continuous (fun s : ℝ => C*(s/4)^gamma) :=
      continuous_const.mul ((Real.continuous_rpow_const hgamma.le).comp (continuous_id.div_const 4))
    apply actual_flat_jet_extension_continuous_four hN hHc hh (by positivity : 0 < R/3)
      (w := fun s : ℝ => C*(s/4)^gamma) hw.continuousAt
      (by simp only [zero_div,Real.zero_rpow hgamma.ne',mul_zero])
    intro x hx hnear
    exact (J.interior_error x hx (by linarith)).2
  have hcl := actualFlatUpperBallFour_closure_subset N (1/8 : ℝ)
  have hcl1 : closure (actualFlatUpperBallFour N (1/8 : ℝ)) ⊆ actualFlatClosedUpperBallFour N 1 := by
    intro x hx
    have hc := hcl hx
    exact ⟨closedBall_subset_closedBall (by norm_num) hc.1,hc.2⟩
  exact {
    derivative := actualFlatJetExtensionFour N (fderiv ℝ D.solution) g
    hessian := actualFlatJetExtensionFour N (realHessian D.solution) h
    continuous_value := D.solution_continuous.mono hcl1
    continuous_derivative := hgrad.mono hcl
    continuous_hessian := hhess.mono hcl
    derivative_eq := by
      intro x hx
      exact if_pos hx.2
    hessian_eq := by
      intro x hx
      exact if_pos hx.2
  }

theorem actual_flat_closure_C2_jet_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B)
    {N : E} (hN : ‖N‖=1)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B) :
    Nonempty (ClosureC2Jet D.solution (actualFlatUpperBallFour N (1/8 : ℝ))) := by
  obtain ⟨R,hR,hR1,gamma,hg,hg1,hga,M,hM,T,hT,beta,hbeta,hbeta1,H,hH,C,hC,hcontrol⟩ :=
    actual_flat_full_jet_control_four hlam hLambda halpha hKa hKf hF hB N hN
  obtain ⟨J⟩ := hcontrol D
  exact ⟨actualFlatClosureC2JetFour hN hR hg hbeta D J⟩

end PowerConvexity
