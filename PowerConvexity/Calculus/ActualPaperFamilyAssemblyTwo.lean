import PowerConvexity.Calculus.ActualClassicalMinkowskiExistenceTwo
import PowerConvexity.Calculus.ActualOriginalMinkowskiCommonCollarTwo

/-! # One actual family closes both frozen original-route interfaces

This statement constructs the actual classical family, retains the prescribed
endpoint, identifies its ball endpoint on the genuine closed ball, chooses
its true closure jets, proves one common small truncation thickness, and
feeds that exact same-family boundary result to the accepted exhaustion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance apfaRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance apfaRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "I" => Icc (0:ℝ) 1

theorem actual_paper_family_common_collar_exhaustion_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hAK : IsCompact (closure A))
    (hsmooth : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u1 : E→ℝ} (hu1 : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) A u1)
    {R rho L : ℝ} (hR : 0<R) (hrho : 0<rho) (hL : 0≤L)
    (hballA : closedBall (0:E) rho⊆A) (hballB : closedBall (0:E) rho⊆ball 0 R)
    (hAb : ∀ x∈A, ‖x‖≤L) (hBb : ∀ x∈ball (0:E) R, ‖x‖≤L) :
    ∃ u : I→E→ℝ,
      ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u ∧
      u ⟨1,by norm_num⟩=u1 ∧
      EqOn (u ⟨0,by norm_num⟩) (quadraticBallPotential 1 R) (closure (ball (0:E) R)) ∧
      ∃ J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)),
      ∃ thickness>0, thickness≤rho ∧ thickness≤1 ∧
        (∀ eps : ℝ, 0<eps → eps<thickness → ∀ t:I,
          ∀ x∈frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
            0<modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
        ∀ t:I,
          (∀ x∈minkowskiDomain t A (ball 0 R),
            0<modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
          StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  letI : Nontrivial E := ⟨⟨e 0,0,e.ne_zero 0⟩⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  obtain ⟨u,hu,hend⟩ := actual_classical_minkowski_family_exists_two hA hAn hconv hAK
    hsmooth e hab hu1 hR
  have hzero := hu.endpoint_zero hab hAn hR
  let J := fun t => Classical.choice (hu t).2.1
  obtain ⟨thickness,hthickness,htr,ht1,hboundary⟩ :=
    actual_original_minkowski_common_truncation_sigma_two hA hconv hAK e hab hR hrho hballA hu
  have hQ : IsCompact (closedBall (0:E) (1:ℝ)) := isCompact_closedBall _ _
  have hQi : (interior (closedBall (0:E) (1:ℝ))).Nonempty := by
    refine ⟨0,?_⟩
    rw [interior_closedBall (0:E) (by norm_num : (1:ℝ)≠0)]
    exact mem_ball_self (by norm_num)
  refine ⟨u,hu,hend,hzero,J,thickness,hthickness,htr,ht1,hboundary,?_⟩
  exact minkowski_actual_exhaustion_from_small_truncation_boundary_two
    (volume : Measure E) hQ hQi e hab hA hconv hAK hsmooth hR hrho hL hthickness
    hballA hballB hAb hBb hu J hboundary

end PowerConvexity
