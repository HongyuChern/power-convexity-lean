import PowerConvexity.Calculus.MinkowskiStrongCommonGeometryHolderTwo
import PowerConvexity.Calculus.StrongDefiningCommonFrameGeometryTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # Actual common Hessian modulus for the complete strong Minkowski family

Every geometric scale, defining-function jet bound, normal margin and C2
solution bound is now constructed from the genuine strong defining data.
The same true classical solution and its actual closure jet are estimated.
The constants precede all parameters and all solutions; no common geometry,
boundary modulus, coefficient Holder bound or third-jet input remains.
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
local instance scahRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance scahRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "V" => AmbientSpace (2+2)
local notation "I" => Icc (0 : ℝ) 1
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem strong_defining_minkowski_actual_boundary_holder_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∀ x ∈ frontier A, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈A ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hfH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    {rho0 Dout : ℝ} (hrho0 : 0 < rho0)
    (hballA : closedBall (0 : E) rho0 ⊆ A)
    (hballB : closedBall (0 : E) rho0 ⊆ ball (0 : E) R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ Dout) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ Dout) :
    ∃ radius > 0, radius ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ t : I, ∀ u : E → ℝ,
      ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (minkowskiDomain t A (ball 0 R)) u →
      ∀ J : ClosureC2Jet u (minkowskiDomain t A (ball 0 R)),
      ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ x ∈ closure (minkowskiDomain t A (ball 0 R)), ‖x-c‖ < radius →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho0.le)⟩
  have hDout : 0 ≤ Dout := by
    simpa only [norm_zero] using hAb 0 (hballA (mem_closedBall_self hrho0.le))
  obtain ⟨T,hTa,hTb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  obtain ⟨r,hr,hr1,Hchart,hHchart,Fchart,hFchart,margin,hmargin,hgeos⟩ :=
    strong_defining_minkowski_actual_common_frame_geometry_two
      hA hconv hK hf hfb hdelta hfH e hab T hR hrho0 hballA hballB hAb hBb
  let Geo : I → ActualCommonNonlinearBoundaryGeometryFour r Hchart Fchart margin rho0 Dout :=
    fun t => Classical.choose (hgeos t t.2)
  have hGeo : ∀ t : I, (Geo t).domain=T ⁻¹' minkowskiDomain t A (ball (0 : E) R) :=
    fun t => Classical.choose_spec (hgeos t t.2)
  exact strong_defining_minkowski_boundary_holder_of_common_geometry_two
    hA hconv hK hAn hf hfb hdelta hfH e hab hR T hTa hTb
    hr hr1 hHchart hmargin hrho0 hDout hFchart.le Geo hGeo


theorem strong_defining_minkowski_actual_global_holder_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∀ x ∈ frontier A, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈A ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hfH : ∀ x ∈ frontier A, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    {rho0 Dout : ℝ} (hrho0 : 0 < rho0)
    (hballA : closedBall (0 : E) rho0 ⊆ A)
    (hballB : closedBall (0 : E) rho0 ⊆ ball (0 : E) R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ Dout) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ Dout) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ t : I, ∀ u : E → ℝ,
      ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (minkowskiDomain t A (ball 0 R)) u →
      ∀ J : ClosureC2Jet u (minkowskiDomain t A (ball 0 R)),
      ∀ x ∈ closure (minkowskiDomain t A (ball 0 R)),
      ∀ y ∈ closure (minkowskiDomain t A (ball 0 R)),
        ‖J.hessian x-J.hessian y‖ ≤ C*‖x-y‖^alpha := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho0.le)⟩
  have hDout : 0 ≤ Dout := by
    simpa only [norm_zero] using hAb 0 (hballA (mem_closedBall_self hrho0.le))
  obtain ⟨T,hTa,hTb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  obtain ⟨r,hr,hr1,Hchart,hHchart,Fchart,hFchart,margin,hmargin,hgeos⟩ :=
    strong_defining_minkowski_actual_common_frame_geometry_two
      hA hconv hK hf hfb hdelta hfH e hab T hR hrho0 hballA hballB hAb hBb
  let Geo : I → ActualCommonNonlinearBoundaryGeometryFour r Hchart Fchart margin rho0 Dout :=
    fun t => Classical.choose (hgeos t t.2)
  have hGeo : ∀ t : I, (Geo t).domain=T ⁻¹' minkowskiDomain t A (ball (0 : E) R) :=
    fun t => Classical.choose_spec (hgeos t t.2)
  exact strong_defining_minkowski_global_holder_of_common_geometry_two
    hA hconv hK hAn hf hfb hdelta hfH e hab hR T hTa hTb
    hr hr1 hHchart hmargin hrho0 hDout hFchart.le Geo hGeo

end PowerConvexity
