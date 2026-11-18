import PowerConvexity.Analysis.ActualWeakQuadraticFrozenUnitBallTwo
import PowerConvexity.Analysis.ActualUniformHolderFrozenBallsTwo

/-! # Uniform frozen weak balls with no coefficient derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_weak_quadratic_holder_balls_two
    {rho lam Lambda K alpha epsilon : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hehalf : epsilon ≤ 1/2) :
    ∃ r > 0, r ≤ 1 ∧ ∀ x₀ : E, ∀ U : Set E,
      IsOpen U → Bornology.IsBounded U → closedBall x₀ rho ⊆ U →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ i j, ContinuousOn (fun y => A.a y i j) (closure U)) →
      ActualWeakQuadraticSourcesTwo A →
      (∀ x ∈ closedBall x₀ rho, ∀ y ∈ closedBall x₀ rho,
        ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤
          K*‖x-y‖^alpha) →
      ∀ x ∈ ball x₀ (rho/4), ∀ G : E ≃L[ℝ] E,
      actualLinearCongruenceMatrixTwo G (A.a x) = 1 →
      ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
      closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
      ∀ (f u : E → ℝ), MemLp f 2 (volume.restrict U) →
      ActualScalarWeakEquationTwo A f u →
      ∃ B : EllipticCoeff (2+2) (ball (0 : E) 1),
        B.lam = 1/2 ∧ B.Λ ≤ max (1/2) (Lambda*(max 1 (Real.sqrt lam)⁻¹)^2) ∧
        (∀ z, B.a z = (actualLinearPullbackCoeffTwo G A).a (G.symm x+r • z)) ∧
        B.a 0 = 1 ∧
        (∀ i j, ContinuousOn (fun z => B.a z i j) (closedBall (0 : E) 1)) ∧
        ActualWeakQuadraticSourcesTwo B ∧
        (∀ z ∈ ball (0 : E) 1, ∀ v : E,
          ‖v-matMulE (B.a z) v‖ ≤ (epsilon*‖z‖^alpha)*‖v‖) ∧
        ActualScalarWeakEquationTwo B
          (fun z => r^2*f (G (G.symm x+r • z)))
          (fun z => u (G (G.symm x+r • z))) := by
  obtain ⟨r,hr,hr1,hscale⟩ := actual_uniform_holder_physical_radius_two hrho
    (Real.sqrt_pos.mpr hLambda) (inv_pos.mpr (Real.sqrt_pos.mpr hlam)) hK halpha hepsilon
  refine ⟨r,hr,hr1,?_⟩
  intro x₀ U hU hUb hclosed A hlo hhi hreg hquad hhold x hx G hfreeze
  have hxU : x ∈ U := hclosed
    ((closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)) (ball_subset_closedBall hx))
  obtain ⟨hGn,hHn⟩ := actual_frozen_normalization_bounds_from_constants_two hU A
    (fun i j => (hreg i j).mono subset_closure) hlam hLambda hlo hhi hxU G hfreeze
  obtain ⟨hcb,hdev⟩ := hscale x₀ U hclosed A.a hhold x hx G hGn hHn hfreeze
  refine ⟨hGn,hHn,hcb,?_⟩
  intro f u hf hu
  obtain ⟨B,hBl,hBL,hBa,hB0,hBr,hBd,hBdev,hBw⟩ :=
    actual_given_weak_quadratic_holder_unit_ball_two hU hUb A G x hfreeze hreg hquad
      halpha hr hepsilon hehalf hcb hdev hf hu
  refine ⟨B,hBl,?_,hBa,hB0,hBr,hBd,hBdev,hBw⟩
  rw [hBL]
  apply max_le_max_left
  change A.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2 ≤
    Lambda*(max 1 (Real.sqrt lam)⁻¹)^2
  apply mul_le_mul hhi _ (sq_nonneg _) hLambda.le
  have hm := max_le_max_left (1 : ℝ) hHn
  nlinarith [le_max_left (1 : ℝ) ‖G.symm.toContinuousLinearMap‖,
    le_max_left (1 : ℝ) (Real.sqrt lam)⁻¹]

end PowerConvexity
