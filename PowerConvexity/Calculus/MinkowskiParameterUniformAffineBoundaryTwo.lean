import PowerConvexity.Calculus.MinkowskiParameterUniformBoundaryGeometryTwo
import PowerConvexity.Calculus.ParameterAffineTangencyTwo

/-! # One affine tangency error bound on all nearby actual boundaries

The constants precede the parameter, the actual boundary center, the unit
tangent direction, and the second actual boundary point. The affine fields
are complex linear, have real trace zero, and are evaluated against actual
spatial derivatives of one jointly C4 defining family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mpuabRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mpuabRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance mpuabDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mpuabDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance mpuabDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance mpuabHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mpuabHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance mpuabHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem classicalDirichlet_minkowski_exists_parameter_uniform_affine_boundary_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ F : ℝ × E → ℝ,
      ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∃ C > 0, ∃ M ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => F (t,x)) ∧
        ∀ x ∈ frontier (V t), F (t,x) = 0 ∧ fderiv ℝ (fun y => F (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ F (t,z) < 0) ∧
          ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ (fun y => F (t,y)) x tau = 0 →
          ∃ (K : E →L[ℂ] E) (c : E),
            (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
            ∀ y ∈ frontier (V t),
              |fderiv ℝ (fun z => F (t,z)) y (c+K y)| ≤ C*‖y-x‖^2 := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d,hd,F,hF,R0,hR0,eta,heta,A,hA,L,hL,hgeometry⟩ :=
    classicalDirichlet_minkowski_exists_parameter_uniform_global_boundary_geometry_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  let G : closedBall s d → E → ℝ := fun t x => F ((t : ℝ),x)
  obtain ⟨C,hC,hquad⟩ := affine_complex_tangency_uniform_family_two G e
    hR0.le heta hA.le hL.le
    (fun t y hy => ((hgeometry t t.property).2.1 y hy).1)
    (fun t y hy => ((hgeometry t t.property).2.1 y hy).2.1)
    (fun t y hy => ((hgeometry t t.property).2.1 y hy).2.2)
  refine ⟨d,hd,F,hF,C,hC,2*A/eta,by positivity,?_⟩
  intro t ht hI
  have hactual := (hgeometry t ht).2.2 hI
  refine ⟨(hgeometry t ht).1,?_⟩
  intro x hx
  have hxd := hactual.2 x hx
  have hxball : x ∈ closedBall (0 : E) R0 := by
    simpa only [mem_closedBall,dist_zero_right] using hxd.1
  have hDn : fderiv ℝ (fun y => F (t,y)) x ≠ 0 :=
    norm_pos_iff.mp (heta.trans_le hxd.2.2.1)
  refine ⟨hxd.2.1,hDn,hxd.2.2.2.1,?_⟩
  intro tau htau htangent
  obtain ⟨K,c,htrace,hcx,hKn,herr⟩ :=
    hquad ⟨t,ht⟩ x hxball hxd.2.2.1 hxd.2.1 tau htau htangent
  refine ⟨K,c,htrace,hcx,hKn,?_⟩
  intro y hy
  have hyd := hactual.2 y hy
  have hyball : y ∈ closedBall (0 : E) R0 := by
    simpa only [mem_closedBall,dist_zero_right] using hyd.1
  exact herr y hyball hyd.2.1

end
end PowerConvexity
