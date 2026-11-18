import PowerConvexity.Analysis.ActualCommonNonlinearGlobalHolderTwo

/-! # Determinant-one Hessian estimates before the actual moving domain

These are the constant-density applications of the true common nonlinear
boundary and global estimates. No density derivative, supplied modulus,
or solution third-derivative bound remains in the interface.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_common_dirichlet_boundary_hessian_holder_two
    {r Hchart F delta rho0 Dout G H : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=1) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      ∀ c ∈ frontier Geo.domain, ∀ x ∈ closure Geo.domain, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨R,hR,hR1,alpha,ha,ha1,C,hC,hbound⟩ :=
    actual_common_nonlinear_closure_boundary_hessian_modulus_two
      (P := 0) (D := 1) (Csrc := 0) hr hr1 hHchart hdelta hrho0 hDout
      hG hH le_rfl hF le_rfl le_rfl
  refine ⟨R,hR,hR1,alpha,ha,ha1,C,hC,?_⟩
  intro Geo u hu J hzero hpos hdet hJu hJH
  apply hbound Geo u (fun _ => 1) hu contDiffOn_const continuousOn_const J
    hzero hpos (by simpa only [Complex.ofReal_one] using hdet)
    (by intro x hx; exact ⟨le_rfl,le_rfl⟩) hJu hJH
  · intro x hx
    simp only [fderiv_const_apply, norm_zero, le_refl]
  · intro x hx v
    simp [realHessian]

theorem actual_common_dirichlet_global_hessian_holder_two
    {r Hchart F delta rho0 Dout G H : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=1) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      ∀ x ∈ closure Geo.domain, ∀ y ∈ closure Geo.domain,
        ‖J.hessian x-J.hessian y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨alpha,ha,ha1,C,hC,hbound⟩ :=
    actual_common_nonlinear_global_holder_two
      (P := 0) (D := 1) (Csrc := 0) hr hr1 hHchart hdelta hrho0 hDout
      hG hH le_rfl hF le_rfl le_rfl
  refine ⟨alpha,ha,ha1,C,hC,?_⟩
  intro Geo u hu J hzero hpos hdet hJu hJH
  apply hbound Geo u (fun _ => 1) hu contDiffOn_const continuousOn_const J
    hzero hpos (by simpa only [Complex.ofReal_one] using hdet)
    (by intro x hx; exact ⟨le_rfl,le_rfl⟩) hJu hJH
  · intro x hx
    simp only [fderiv_const_apply, norm_zero, le_refl]
  · intro x hx v
    simp [realHessian]

end PowerConvexity
