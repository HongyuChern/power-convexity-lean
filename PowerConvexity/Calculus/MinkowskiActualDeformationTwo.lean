import PowerConvexity.Calculus.MinkowskiComplexFrameMinimumTwo
import PowerConvexity.Calculus.ActualDomainDeformationTwo
import PowerConvexity.Calculus.ClassicalMinkowskiEndpointsTwo

/-! # The physical Minkowski path from the actual ball endpoint

This assembly derives the initial spectral positivity from comparison with
the explicit ball solution. It derives one admissible perturbation radius,
its boundary positivity, and continuity of its actual minimum from the jet
estimate. The remaining inputs are the classical family, the local boundary
upper estimate, and unperturbed spectral positivity on a common truncation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem ClassicalMinkowskiFamilyTwo.ball_endpoint_sigma_positive
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAn : A.Nonempty) {R : ℝ} (hR : 0 < R)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    {x : E} (hx : x ∈ ball 0 R) :
    0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u ⟨0,by norm_num⟩) x := by
  let t₀ : I := ⟨0,by norm_num⟩
  have hdata := hu t₀
  change ClassicalDirichletDataTwo e (fun j => Complex.I • e j)
    (minkowskiDomain 0 A (ball 0 R)) (u t₀) at hdata
  rw [minkowskiDomain_zero hAn] at hdata
  have he := hu.endpoint_zero hab hAn hR
  have hEq : u t₀ =ᶠ[𝓝 x] quadraticBallPotential 1 R := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he (subset_closure hy)
  have hEqP : powerTransform (u t₀) =ᶠ[𝓝 x] powerTransform (quadraticBallPotential 1 R) := by
    filter_upwards [hEq] with y hy
    simp only [powerTransform,hy]
  have hH : realHessian (powerTransform (u t₀)) x =
      realHessian (powerTransform (quadraticBallPotential 1 R)) x :=
    (hEqP.fderiv (𝕜 := ℝ)).fderiv_eq
  have hneg : u t₀ x < 0 := by
    rw [hEq.eq_of_nhds]
    exact quadraticBallPotential_negative (by norm_num) hR hx
  apply (modifiedSigmaTwo_pos_iff_powerHessian_pos e
    ((hdata.1.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by norm_num)) hneg
    (hdata.2.2.1 x hx)).mpr
  rw [hH]
  exact quadraticBallPotential_powerHessian_pos (by norm_num) hR hx

theorem minkowski_actual_deformation_from_boundary_sigma_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A) {R ρ L ε : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hbound : ∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ z ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian z v v ≤ M*‖v‖^2)
    (hboundary : ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∃ η > 0, ∀ t : I, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η →
      (∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x) ∧
      StrictConvexOn ℝ (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε)
        (powerTransform (fun y => u t y+q y)) := by
  let V : I → Set E := fun t => distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε
  have hgeo (t : I) := minkowski_distanceInterior_uniform_geometry hAo isOpen_ball
    hA (convex_ball 0 R) hρ hε hερ hballA hballB hAb hBb t
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball hAn t
  have hcl (t : I) : closure (V t) ⊆ minkowskiDomain t A (ball 0 R) := (hgeo t).2.2.2.2
  obtain ⟨η,hη,hnegative,hbd,hm⟩ := minkowski_complexFrame_exists_common_quadratic_radius_two
    μ hK hKi e hab hAo isOpen_ball hA (convex_ball 0 R) hρ hL hε hερ
    hballA hballB hAb hBb hu J hbound hboundary
  refine ⟨η,hη,?_⟩
  apply constantDensity_quadratic_actual_domain_deformation_two μ hK hKi e
    (V := V) (fun t => (hgeo t).1) (fun t => (hgeo t).2.1)
    (fun t => (hgeo t).2.2.2.1) (fun t => ⟨0,(hgeo t).2.2.1⟩)
    u (fun _ => 1)
    (fun t x hx => (hu t).1.contDiffAt ((hU t).mem_nhds (hcl t hx)))
    (fun _ => one_ne_zero)
    (fun t x hx => (hu t).2.2.2.1 x (hcl t (subset_closure hx)))
    (fun t x hx => (hu t).2.2.1 x (hcl t hx)) hη hnegative
    ⟨0,by norm_num⟩ ?_ hbd hm
  intro x hx
  apply hu.ball_endpoint_sigma_positive e hab hAn hR
  have hxU := hcl ⟨0,by norm_num⟩ hx
  simpa only [minkowskiDomain_zero hAn] using hxU

end PowerConvexity
