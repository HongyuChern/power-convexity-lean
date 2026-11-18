import PowerConvexity.Calculus.ActualOriginalDomainPowerConvexityTwo
import PowerConvexity.Calculus.MinkowskiActualCollarExhaustionTwo

/-! # Exact original-family common truncation interface

The alternative strong-approximation proof has already returned positivity
to the same actual solution on each original Minkowski domain. Thus it gives
the actual frontiers of all positive distance truncations. The common small
thickness is chosen before both truncation and parameter, and is passed to
the original accepted exhaustion theorem. No original collar hypothesis or
old final power-convexity endpoint enters this proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance aomccRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance aomccRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "I" => Icc (0:ℝ) 1

theorem actual_original_minkowski_all_positive_truncations_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (h0 : (0:E)∈A) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0<R) {u : I→E→ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u) :
    ∀ eps : ℝ, 0<eps → ∀ t:I,
      ∀ x∈frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
        0<modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  have hBK : IsCompact (closure (ball (0:E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  intro eps heps t x hx
  have hVo : IsOpen (minkowskiDomain t A (ball (0:E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,h0⟩ t
  have hVc := minkowskiDomain_convex hconv (convex_ball (0:E) R) (t:ℝ)
  have hVK : IsCompact (closure (minkowskiDomain t A (ball (0:E) R))) := by
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul (t:ℝ)).add (hBK.smul (1-(t:ℝ)))
  have hV0 : (0:E)∈minkowskiDomain t A (ball 0 R) :=
    minkowskiDomain_contains_inter t A (ball (0:E) R) ⟨h0,mem_ball_self hR⟩
  have hp := actual_original_dirichlet_hessian_sigma_strictConvex_two hVo hVc hVK hV0 e hab (hu t)
  exact hp.2.1 x (distanceInteriorDomain_frontier_value hVo heps x hx).1

theorem actual_original_minkowski_common_truncation_sigma_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho : ℝ} (hR : 0<R) (hrho : 0<rho)
    (hballA : closedBall (0:E) rho⊆A) {u : I→E→ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u) :
    ∃ thickness>0, thickness≤rho ∧ thickness≤1 ∧
      ∀ eps : ℝ, 0<eps → eps<thickness → ∀ t:I,
        ∀ x∈frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          0<modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  refine ⟨min rho 1,lt_min hrho (by norm_num),min_le_left _ _,min_le_right _ _,?_⟩
  intro eps heps _heps
  exact actual_original_minkowski_all_positive_truncations_two hA hconv hK
    (hballA (mem_closedBall_self hrho.le)) e hab hR hu eps heps

theorem actual_original_minkowski_exhaustion_two
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hAK : IsCompact (closure A))
    (hsmooth : HasSmoothLocalDefiningFunction A)
    {R rho L : ℝ} (hR : 0<R) (hrho : 0<rho) (hL : 0≤L)
    (hballA : closedBall (0:E) rho⊆A) (hballB : closedBall (0:E) rho⊆ball 0 R)
    (hAb : ∀ x∈A, ‖x‖≤L) (hBb : ∀ x∈ball (0:E) R, ‖x‖≤L)
    {u : I→E→ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∀ t:I,
      (∀ x∈minkowskiDomain t A (ball 0 R),
        0<modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  obtain ⟨thickness,hthickness,_htr,_ht1,hboundary⟩ :=
    actual_original_minkowski_common_truncation_sigma_two hA hconv hAK e hab hR hrho hballA hu
  exact minkowski_actual_exhaustion_from_small_truncation_boundary_two mu hK hKi e hab
    hA hconv hAK hsmooth hR hrho hL hthickness hballA hballB hAb hBb hu J hboundary

end PowerConvexity
