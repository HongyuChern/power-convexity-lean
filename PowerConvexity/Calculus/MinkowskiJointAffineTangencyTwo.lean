import PowerConvexity.Calculus.ParameterAffineTangencyTwo
import PowerConvexity.Calculus.MinkowskiJointGeometryBounds
import PowerConvexity.Calculus.AffineBoundaryJetQuadraticBoundTwo

/-! # Uniform actual affine tangent fields on nearby Minkowski boundary charts

One quadratic constant, one field norm cap and one radius precede the parameter,
the actual moving boundary point and the unit tangent direction. The defining
functions and all their geometric bounds are constructed from the original
smooth convex domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mjatInstance1 : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mjatInstance2 : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance mjatInstance3 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mjatInstance4 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance mjatInstance5 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance mjatInstance6 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mjatInstance7 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance mjatInstance8 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem minkowskiDomain_exists_parameter_uniform_affine_tangency_two
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {p : E} (hp : p ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,p) ∧ phi (s,p) = 0 ∧
      ∃ C > 0, ∃ M ≥ 0, ∃ r > 0,
        ∀ t ∈ closedBall s r, t ∈ Icc (0 : ℝ) 1 →
          (∀ x ∈ closedBall p r,
            ∀ᶠ z in 𝓝 x, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ phi (t,z) < 0) ∧
          (∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), x ∈ closedBall p r →
            ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ (fun z => phi (t,z)) x tau = 0 →
              ∃ (K : E →L[ℂ] E) (c : E),
                (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
                ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), y ∈ closedBall p r →
                  |fderiv ℝ (fun z => phi (t,z)) y (c+K y)| ≤ C*‖y-x‖^2) := by
  obtain ⟨phi,hphi,hphi0,eta,heta,A,hA,L,hL,r,hr,hbounds⟩ :=
    minkowskiDomain_exists_joint_uniform_C3_defining_bounds hU hconv hK hboundary hs hs1 hR hp
  let I := {t : ℝ // t ∈ closedBall s r}
  have hpair (t : I) (y : E) (hy : y ∈ closedBall p r) :
      ((t : ℝ),y) ∈ closedBall (s,p) r := by
    rw [← closedBall_prod_same]
    exact ⟨t.2,hy⟩
  obtain ⟨C,hC,hquad⟩ := affine_complex_tangency_uniform_family_two
    (fun t : I => fun y : E => phi ((t : ℝ),y)) e hr.le heta hA.le hL.le
    (fun t y hy => (hbounds ((t : ℝ),y) (hpair t y hy)).1)
    (fun t y hy => (hbounds ((t : ℝ),y) (hpair t y hy)).2.2.1)
    (fun t y hy => (hbounds ((t : ℝ),y) (hpair t y hy)).2.2.2.1)
  let d := min r (s/2)
  have hd : 0 < d := lt_min hr (half_pos hs)
  have hdr : d ≤ r := min_le_left _ _
  refine ⟨phi,hphi,hphi0,C,hC,2*A/eta,by positivity,d,hd,?_⟩
  intro t ht hI
  have htr : t ∈ closedBall s r := (closedBall_subset_closedBall hdr) ht
  have hdist : |t-s| ≤ s/2 := by
    simpa only [Real.dist_eq] using (mem_closedBall.mp ht).trans (min_le_right r (s/2))
  have htpos : 0 < t := by
    have hh := (abs_le.mp hdist).1
    linarith
  have hVo : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ htpos.ne').add_right
  have hb (y : E) (hy : y ∈ closedBall p d) :=
    hbounds (t,y) (hpair ⟨t,htr⟩ y ((closedBall_subset_closedBall hdr) hy))
  constructor
  · intro x hx
    exact (hb x hx).2.2.2.2 hI
  · intro x hx hxball tau htau htangent
    have hfx : phi (t,x) = 0 := local_defining_function_zero_at_frontier
      hVo hx (hb x hxball).1.continuousAt ((hb x hxball).2.2.2.2 hI)
    obtain ⟨K,c,htrace,hcx,hKn,hquadK⟩ := hquad ⟨t,htr⟩ x
      ((closedBall_subset_closedBall hdr) hxball) (hb x hxball).2.1 hfx tau htau htangent
    refine ⟨K,c,htrace,hcx,hKn,?_⟩
    intro y hy hyball
    have hfy : phi (t,y) = 0 := local_defining_function_zero_at_frontier
      hVo hy (hb y hyball).1.continuousAt ((hb y hyball).2.2.2.2 hI)
    exact hquadK y ((closedBall_subset_closedBall hdr) hyball) hfy

end
end PowerConvexity
