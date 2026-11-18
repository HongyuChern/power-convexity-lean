import PowerConvexity.Analysis.ActualConvexBoundaryLinearJetComparisonFour
import PowerConvexity.Analysis.ActualUniformTangentialBoundaryExpansionFour

/-! # Same-function boundary compatibility for the actual nonlinear tangential response

The common affine expansions are compared on the genuine interior probe
ball of the original convex domain. All constants precede the solution,
density, closure jet and unit directions. No boundary Hessian modulus is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_tangential_boundary_compatibility_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hne : U.Nonempty) {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hgb : ∀ c ∈ frontier U, g c=0 ∧ fderiv ℝ g c≠0)
    (hgdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {G H P F : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 1 rho U →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ frontier U, u x=0) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 →
      ∀ c ∈ frontier U, ∀ d ∈ frontier U, ‖c-d‖ < R →
      let T := actualDefiningTangentialFieldFour g e N
      ‖actualClosureTangentialDerivativeFour J T c-
        actualClosureTangentialDerivativeFour J T d‖ ≤ C*‖c-d‖^alpha := by
  obtain ⟨R,hR,alpha,halpha,halpha1,C,hC,Q,hQ,hexp⟩ :=
    actual_uniform_tangential_boundary_expansion_four hU hconv hK hg hgb hgdef
      hG hH hP hF hg1 hg2 hg3
  obtain ⟨o,ho⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU o ho
  let rho0 := r/2
  have hrho : 0 < rho0 := half_pos hr
  have hclosed : closedBall o rho0 ⊆ U := by
    intro x hx
    apply hball
    rw [mem_ball]
    exact (show dist x o ≤ rho0 from hx).trans_lt (half_lt_self hr)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun x : E => o-x) (closure U) from
      (continuous_const.sub continuous_id).continuousOn)
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ D := by
    intro c hc
    exact (hB c (frontier_subset_closure hc)).trans (le_max_left _ _)
  let radius := min 1 (min (R/4) (D+rho0))
  have hradius : 0 < radius := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let K := 72*C*(4 : ℝ)^alpha*(D+rho0)^2/rho0^2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨radius,hradius,min_le_left _ _,alpha,halpha,halpha1,K,hK0,?_⟩
  intro u rho hu hrhoReg J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN c hc d hd hnear
  let T := actualDefiningTangentialFieldFour g e N
  have herr : ∀ a ∈ frontier U, ∀ x ∈ U, ‖x-a‖ < R →
      |actualClosureTangentialResponseFour J T x-
        actualClosureTangentialDerivativeFour J T a (x-a)| ≤ C*‖x-a‖*‖x-a‖^alpha := by
    intro a ha
    exact (hexp u rho hu hrhoReg J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN a ha).2
  exact actual_convex_boundary_linear_derivative_holder_four hU hconv hrho hD hR hC
    halpha.le hclosed frontier_subset_closure hbound herr c hc d hd
    (hnear.trans_le (min_le_right _ _))

end PowerConvexity
