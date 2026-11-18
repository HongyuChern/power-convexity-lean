import PowerConvexity.Calculus.MinkowskiParameterUniformBoundaryTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets
import PowerConvexity.Analysis.CompactLocalMonotoneBounds

/-! # Actual noncircular family bounds and joint jets at positive parameters

Existence of the actual family remains an input. No boundary Hessian estimate
is an input at a positive parameter: it follows from the given endpoint data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_boundary_upper_eventually_of_pos_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {s : I} (hs : 0 < (s : ℝ)) :
    ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s, ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2 := by
  let one : I := ⟨1,by norm_num⟩
  have he : minkowskiDomain (one : ℝ) A (ball (0 : E) R) = A :=
    minkowskiDomain_one ⟨0,mem_ball_self hR⟩
  have hdata : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) A (u one) := by
    simpa only [he] using hu one
  have Jone : ClosureC2Jet (u one) A := by simpa only [he] using J one
  obtain ⟨d,hd,M,hM,hbound⟩ :=
    classicalDirichlet_minkowski_parameter_uniform_boundary_quadratic_upper_two
      hA hconv hK hboundary (hdata.1.of_le (by norm_num)) Jone hdata.2.2.2.2
      e hab hdata.2.2.1 hdata.2.2.2.1 hs s.2.2 hR
  have hnear : ∀ᶠ t : I in 𝓝 s, (t : ℝ) ∈ closedBall (s : ℝ) d :=
    continuous_subtype_val.continuousAt.tendsto.eventually (closedBall_mem_nhds (s : ℝ) hd)
  refine ⟨M,hM,?_⟩
  filter_upwards [hnear] with t ht
  exact hbound t ht t.2 (u t) (J t) ((hu t).1.of_le (by norm_num))
    (hu t).2.2.2.2 (hu t).2.2.1 (hu t).2.2.2.1

theorem minkowski_family_uniform_boundary_upper_away_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ M ≥ 0, ∀ t : I, a ≤ (t : ℝ) → ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2 := by
  let K : Set I := {t | a ≤ (t : ℝ)}
  have hKc : IsCompact K := isCompact_univ.of_isClosed_subset
    (isClosed_le continuous_const continuous_subtype_val) (subset_univ K)
  let P : I → ℝ → Prop := fun t M => ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)),
    ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2
  apply compact_uniform_monotone_bound_of_local hKc P
  · intro t M N hMN hP x hx v
    exact (hP x hx v).trans (mul_le_mul_of_nonneg_right hMN (sq_nonneg ‖v‖))
  · intro s hs
    exact minkowski_family_boundary_upper_eventually_of_pos_two hA hconv hK hboundary
      e hab hR hu J (ha.trans_le hs)

theorem minkowski_family_actual_jets_continuousAt_of_pos_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {s : I} (hs : 0 < (s : ℝ)) {x : E} (hx : x ∈ minkowskiDomain s A (ball 0 R)) :
    ContinuousAt (fun p : I × E => fderiv ℝ (u p.1) p.2) (s,x) ∧
    ContinuousAt (fun p : I × E => realHessian (u p.1) p.2) (s,x) := by
  have hbound := minkowski_family_boundary_upper_eventually_of_pos_two
    hA hconv hK hboundary e hab hR hu J hs
  exact minkowski_classicalDirichlet_complexFrame_jets_of_boundary_upper_two e hab
    hA isOpen_ball hconv (convex_ball 0 R) hrho hL hballA hballB hAb hBb hu J hx hbound

end PowerConvexity
