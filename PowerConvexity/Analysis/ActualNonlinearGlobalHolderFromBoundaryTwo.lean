import PowerConvexity.Analysis.ActualBoundaryInteriorPowerGluingFour
import PowerConvexity.Analysis.ActualUniformRescaledDensityHessianHolderTwo
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # Actual global nonlinear Hessian Holder control from the proved boundary modulus

The radius-uniform nonlinear interior estimate and a common actual boundary
estimate are applied to the same solution and closure jet. The resulting
positive exponent and constant precede every solution in the common-data
class; continuity extends the estimate to the entire original closure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_nonlinear_global_holder_from_boundary_two
    {H D P Csrc R gamma C : ℝ} (hH : 0 ≤ H) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hCsrc : 0 ≤ Csrc) (hR : 0 < R) (hgamma : 0 < gamma) (hC : 0 ≤ C) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ K ≥ 0,
      ∀ U : Set E, IsOpen U → U≠univ → Convex ℝ U →
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 2 rho U →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x ∧ rho x ≤ D) →
      (∀ x ∈ closure U, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ U, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      (∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^gamma) →
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖J.hessian x-J.hessian y‖ ≤ K*‖x-y‖^alpha := by
  obtain ⟨beta,I,hbeta,hbeta1,hI,hinner⟩ :=
    actual_uniform_rescaled_density_hessian_holder_two hH hD hP hCsrc
  obtain ⟨K,hK,hglue⟩ := actual_boundary_interior_power_gluing_four hbeta hgamma hR hH hC
    (show 0 ≤ 16*I by positivity)
  let alpha := min beta gamma/2
  have halpha : 0 < alpha := div_pos (lt_min hbeta hgamma) (by norm_num)
  have halpha1 : alpha < 1 := by
    have hh := min_le_left beta gamma
    dsimp only [alpha]
    linarith
  refine ⟨alpha,halpha,halpha1,K,hK,?_⟩
  intro U hU hproper hconv u rho hu hrho J hpos hdet hrhob hJH hrhoD hsource hboundary
  have huH : ∀ x ∈ U, ‖realHessian u x‖ ≤ H := by
    intro x hx
    change ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H
    rw [← J.hessian_eq hx]
    exact hJH x (subset_closure hx)
  have hrhoLip : ∀ x ∈ U, ∀ y ∈ U, |rho x-rho y| ≤ P*‖x-y‖ := by
    intro x hx y hy
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hrho.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      hrhoD hconv hy hx
  apply actual_holder_bound_on_closure_four (Z := E →L[ℝ] E →L[ℝ] ℝ)
    (U := U) (f := J.hessian) J.continuous_hessian halpha.le
  apply hglue (E →L[ℝ] E →L[ℝ] ℝ) U hU hproper J.hessian
    (fun x hx => hJH x (subset_closure hx)) hboundary
  intro x hx r hr hr1 hball y hyr
  have hsub : ball x r ⊆ ball x (2*r) := ball_subset_ball (by linarith)
  have hy : y ∈ U := hball (hsub hyr)
  have hinnerH := hinner r hr hr1 x u rho (hu.mono hball) (hrho.mono hball)
    (fun z hz => hdet z (hball hz)) (fun z hz => hpos z (hball hz))
    (fun z hz => hrhob z (hball hz)) (fun z hz => huH z (hball hz))
    (fun z hz w hw => hrhoLip z (hball hz) w (hball hw))
    (fun z hz v => hsource z (hball hz) v) x (mem_ball_self hr) y hyr
  rw [J.hessian_eq hx,J.hessian_eq hy]
  exact (realHessian_norm_sub_le_sixteen_block_norm_two u x y).trans
    ((mul_le_mul_of_nonneg_left hinnerH (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end PowerConvexity
