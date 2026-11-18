import PowerConvexity.Analysis.ActualCommonDirichletHessianHolderTwo
import PowerConvexity.Analysis.ActualUniformIsometricClosureJetTwo
import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo

/-! # Common actual moving-domain Hessian estimates in any isometric frame

The pullback uses one genuine real linear isometry. Its transported frame
and the actual closure jet are identified exactly, including the Hessian
operator norm. Thus the canonical common-domain estimates apply to the
same physical solutions and the same physical boundary points.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "V" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_dirichlet_data_isometric_pullback_two
    (L : V ≃ₗᵢ[ℝ] E) {a b : Fin 2 → E}
    (hLa : ∀ i, L (realDirections i)=a i) (hLb : ∀ i, L (imagDirections i)=b i)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ClassicalDirichletDataTwo a b U u) :
    ClassicalDirichletDataTwo realDirections imagDirections (L ⁻¹' U) (fun x => u (L x)) := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by norm_num)
  have hfr : frontier (L ⁻¹' U)=L ⁻¹' frontier U := (L.toHomeomorph.preimage_frontier U).symm
  have hH (z : V) (hz : z∈L ⁻¹' U) :
      complexHessian realDirections imagDirections (fun x => u (L x)) z=
        complexHessian a b u (L z) := by
    rw [complexHessian_comp_linearIsometry L (hu2.contDiffAt (hU.mem_nhds hz))]
    rw [show (fun i => L (realDirections i))=a from funext hLa,
      show (fun i => L (imagDirections i))=b from funext hLb]
  obtain ⟨J⟩ := hu.2.1
  refine ⟨hu.1.comp L.contDiff.contDiffOn (fun _ hz => hz),
    ⟨actualClosureC2JetIsometricPullbackTwo L hU hu2 J⟩,?_,?_,?_⟩
  · intro z hz
    rw [hH z hz]
    exact hu.2.2.1 (L z) hz
  · intro z hz
    rw [hH z hz]
    exact hu.2.2.2.1 (L z) hz
  · intro z hz
    exact hu.2.2.2.2 (L z) (by rwa [hfr] at hz)

theorem actual_common_frame_dirichlet_boundary_hessian_holder_two
    (L : V ≃ₗᵢ[ℝ] E) {a b : Fin 2 → E}
    (hLa : ∀ i, L (realDirections i)=a i) (hLb : ∀ i, L (imagDirections i)=b i)
    {r Hchart F delta rho0 Dout G H : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ U : Set E, IsOpen U →
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      Geo.domain=L ⁻¹' U → ∀ u : E → ℝ, ClassicalDirichletDataTwo a b U u →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure U, ‖J.hessian x‖ ≤ H) →
      ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨R,hR,hR1,alpha,ha,ha1,C,hC,hmod⟩ :=
    actual_common_dirichlet_boundary_hessian_holder_two hr hr1 hHchart hdelta hrho0 hDout hG hH hF
  refine ⟨R,hR,hR1,alpha,ha,ha1,C,hC,?_⟩
  intro U hU Geo hGeo u hu J hJu hJH c hc x hx hxc
  let W := L ⁻¹' U
  let uL := fun z => u (L z)
  have huL : ClassicalDirichletDataTwo realDirections imagDirections W uL :=
    actual_dirichlet_data_isometric_pullback_two L hLa hLb hU hu
  let JL := actualClosureC2JetIsometricPullbackTwo L hU (hu.1.of_le (by norm_num)) J
  have hcl : closure W=L ⁻¹' closure U := (L.toHomeomorph.preimage_closure U).symm
  have hfr : frontier W=L ⁻¹' frontier U := (L.toHomeomorph.preimage_frontier U).symm
  have hJL1 (z : V) (hz : z∈closure W) : ‖JL.derivative z‖ ≤ G := by
    rw [actual_isometric_closure_jet_derivative_norm_two]
    exact hJu (L z) (by rwa [hcl] at hz)
  have hJL2 (z : V) (hz : z∈closure W) : ‖JL.hessian z‖ ≤ H := by
    rw [actual_isometric_closure_jet_hessian_norm_two]
    exact hJH (L z) (by rwa [hcl] at hz)
  have hcL : L.symm c∈frontier W := by rw [hfr]; simpa only [mem_preimage,L.apply_symm_apply]
  have hxL : L.symm x∈closure W := by rw [hcl]; simpa only [mem_preimage,L.apply_symm_apply]
  have hdist : ‖L.symm x-L.symm c‖=‖x-c‖ := by rw [←L.symm.map_sub,L.symm.norm_map]
  have hmodGeo := hmod Geo
  rw [hGeo] at hmodGeo
  have hh := hmodGeo uL huL.1 JL huL.2.2.2.2 huL.2.2.1 huL.2.2.2.1
    hJL1 hJL2 (L.symm c) hcL (L.symm x) hxL (by rwa [hdist])
  rw [actual_isometric_closure_jet_hessian_difference_two,L.apply_symm_apply,
    L.apply_symm_apply,hdist] at hh
  exact hh

theorem actual_common_frame_dirichlet_global_hessian_holder_two
    (L : V ≃ₗᵢ[ℝ] E) {a b : Fin 2 → E}
    (hLa : ∀ i, L (realDirections i)=a i) (hLb : ∀ i, L (imagDirections i)=b i)
    {r Hchart F delta rho0 Dout G H : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ U : Set E, IsOpen U →
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      Geo.domain=L ⁻¹' U → ∀ u : E → ℝ, ClassicalDirichletDataTwo a b U u →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure U, ‖J.hessian x‖ ≤ H) →
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖J.hessian x-J.hessian y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨alpha,ha,ha1,C,hC,hmod⟩ :=
    actual_common_dirichlet_global_hessian_holder_two hr hr1 hHchart hdelta hrho0 hDout hG hH hF
  refine ⟨alpha,ha,ha1,C,hC,?_⟩
  intro U hU Geo hGeo u hu J hJu hJH x hx y hy
  let W := L ⁻¹' U
  let uL := fun z => u (L z)
  have huL : ClassicalDirichletDataTwo realDirections imagDirections W uL :=
    actual_dirichlet_data_isometric_pullback_two L hLa hLb hU hu
  let JL := actualClosureC2JetIsometricPullbackTwo L hU (hu.1.of_le (by norm_num)) J
  have hcl : closure W=L ⁻¹' closure U := (L.toHomeomorph.preimage_closure U).symm
  have hJL1 (z : V) (hz : z∈closure W) : ‖JL.derivative z‖ ≤ G := by
    rw [actual_isometric_closure_jet_derivative_norm_two]
    exact hJu (L z) (by rwa [hcl] at hz)
  have hJL2 (z : V) (hz : z∈closure W) : ‖JL.hessian z‖ ≤ H := by
    rw [actual_isometric_closure_jet_hessian_norm_two]
    exact hJH (L z) (by rwa [hcl] at hz)
  have hxL : L.symm x∈closure W := by rw [hcl]; simpa only [mem_preimage,L.apply_symm_apply]
  have hyL : L.symm y∈closure W := by rw [hcl]; simpa only [mem_preimage,L.apply_symm_apply]
  have hdist : ‖L.symm x-L.symm y‖=‖x-y‖ := by rw [←L.symm.map_sub,L.symm.norm_map]
  have hmodGeo := hmod Geo
  rw [hGeo] at hmodGeo
  have hh := hmodGeo uL huL.1 JL huL.2.2.2.2 huL.2.2.1 huL.2.2.2.1
    hJL1 hJL2 (L.symm x) hxL (L.symm y) hyL
  rw [actual_isometric_closure_jet_hessian_difference_two,L.apply_symm_apply,
    L.apply_symm_apply,hdist] at hh
  exact hh

end PowerConvexity
