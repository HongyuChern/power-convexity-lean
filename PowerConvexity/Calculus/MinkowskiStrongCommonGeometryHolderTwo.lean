import PowerConvexity.Analysis.ActualCommonFrameDirichletHessianHolderTwo
import PowerConvexity.Calculus.StrongDefiningCommonClosureC2Two

/-! # Actual common Hessian Holder control on strong Minkowski domains

The classical C2 bounds are proved from the original strong defining
function. A common set of genuine physical geometries then yields the
Hessian modulus before selecting any parameter, solution or closure jet.
The geometric records are the only family-level geometric input here;
there is no supplied solution modulus or solution derivative bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance scghRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance scghRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "V" => AmbientSpace (2+2)
local notation "I" => Icc (0 : ℝ) 1
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem strong_defining_minkowski_boundary_holder_of_common_geometry_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hAn : A.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∀ x ∈ frontier A, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈A ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hfH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    (T : V ≃ₗᵢ[ℝ] E)
    (hTa : ∀ i, T (realDirections i)=e i)
    (hTb : ∀ i, T (imagDirections i)=Complex.I • e i)
    {r Hchart Fchart margin rho0 Dout : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hmargin : 0 < margin)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout) (hFchart : 0 ≤ Fchart)
    (Geo : I → ActualCommonNonlinearBoundaryGeometryFour r Hchart Fchart margin rho0 Dout)
    (hGeo : ∀ t : I, (Geo t).domain=T ⁻¹' minkowskiDomain t A (ball 0 R)) :
    ∃ radius > 0, radius ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ t : I, ∀ u : E → ℝ,
      ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (minkowskiDomain t A (ball 0 R)) u →
      ∀ J : ClosureC2Jet u (minkowskiDomain t A (ball 0 R)),
      ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ x ∈ closure (minkowskiDomain t A (ball 0 R)), ‖x-c‖ < radius →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨M,hM,hC2⟩ := strong_defining_minkowski_common_closure_C2_bound_two
    hA hconv hK hAn hf hfb hdelta hfH e hab hR
  obtain ⟨radius,hrad,hrad1,alpha,ha,ha1,C,hC,hmod⟩ :=
    actual_common_frame_dirichlet_boundary_hessian_holder_two T hTa hTb
      hr hr1 hHchart hmargin hrho0 hDout hM hM hFchart
  refine ⟨radius,hrad,hrad1,alpha,ha,ha1,C,hC,?_⟩
  intro t u hu J
  have hVo : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball hAn t
  have hbound := hC2 t t.2 u J hu.1 hu.2.2.2.2 hu.2.2.1 hu.2.2.2.1
  exact hmod _ hVo (Geo t) (hGeo t) u hu J
    (fun x hx => (hbound x hx).1) (fun x hx => (hbound x hx).2)

theorem strong_defining_minkowski_global_holder_of_common_geometry_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hAn : A.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∀ x ∈ frontier A, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈A ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hfH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    (T : V ≃ₗᵢ[ℝ] E)
    (hTa : ∀ i, T (realDirections i)=e i)
    (hTb : ∀ i, T (imagDirections i)=Complex.I • e i)
    {r Hchart Fchart margin rho0 Dout : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hmargin : 0 < margin)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout) (hFchart : 0 ≤ Fchart)
    (Geo : I → ActualCommonNonlinearBoundaryGeometryFour r Hchart Fchart margin rho0 Dout)
    (hGeo : ∀ t : I, (Geo t).domain=T ⁻¹' minkowskiDomain t A (ball 0 R)) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ t : I, ∀ u : E → ℝ,
      ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (minkowskiDomain t A (ball 0 R)) u →
      ∀ J : ClosureC2Jet u (minkowskiDomain t A (ball 0 R)),
      ∀ x ∈ closure (minkowskiDomain t A (ball 0 R)),
      ∀ y ∈ closure (minkowskiDomain t A (ball 0 R)),
        ‖J.hessian x-J.hessian y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨M,hM,hC2⟩ := strong_defining_minkowski_common_closure_C2_bound_two
    hA hconv hK hAn hf hfb hdelta hfH e hab hR
  obtain ⟨alpha,ha,ha1,C,hC,hmod⟩ :=
    actual_common_frame_dirichlet_global_hessian_holder_two T hTa hTb
      hr hr1 hHchart hmargin hrho0 hDout hM hM hFchart
  refine ⟨alpha,ha,ha1,C,hC,?_⟩
  intro t u hu J
  have hVo : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball hAn t
  have hbound := hC2 t t.2 u J hu.1 hu.2.2.2.2 hu.2.2.1 hu.2.2.2.1
  exact hmod _ hVo (Geo t) (hGeo t) u hu J
    (fun x hx => (hbound x hx).1) (fun x hx => (hbound x hx).2)

end PowerConvexity
