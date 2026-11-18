import PowerConvexity.Analysis.ActualHolderFrozenUnitBallTwo

/-! # Frozen actual weak balls uniform over a Holder coefficient family

The ellipticity constants, Holder modulus and interior distance precede the
chosen radius. The C1 hypothesis is qualitative and its norm is never used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_frozen_normalization_bounds_from_constants_two
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U)
    {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlo : lam ≤ A.lam) (hhi : A.Λ ≤ Lambda)
    {x : E} (hx : x ∈ U) (G : E ≃L[ℝ] E)
    (hfreeze : actualLinearCongruenceMatrixTwo G (A.a x) = 1) :
    ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ := by
  have hb := actual_elliptic_bounds_pointwise_two hU A ha x hx
  exact actual_frozen_normalization_operator_bounds_two G hfreeze hlam hLambda
    (fun v => (mul_le_mul_of_nonneg_right hlo (sq_nonneg _)).trans (hb v).1)
    (fun v => (hb v).2.trans (mul_le_mul_of_nonneg_right hhi (sq_nonneg _)))

theorem actual_uniform_holder_frozen_weak_balls_two
    {rho lam Lambda K alpha epsilon : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hehalf : epsilon ≤ 1/2) :
    ∃ r > 0, r ≤ 1 ∧ ∀ x₀ : E, ∀ U : Set E,
      IsOpen U → Bornology.IsBounded U → closedBall x₀ rho ⊆ U →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U) →
      (∀ y ∈ U, ∀ j,
        (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0) →
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
        (∀ i j, ContDiffOn ℝ 1 (fun z => B.a z i j) (ball (0 : E) 2)) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ j,
          (∑ i, fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) = 0) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ v : E,
          ‖v-matMulE (B.a z) v‖ ≤ (epsilon*‖z‖^alpha)*‖v‖) ∧
        ActualScalarWeakEquationTwo B
          (fun z => r^2*f (G (G.symm x+r • z)))
          (fun z => u (G (G.symm x+r • z))) := by
  obtain ⟨r,hr,hr1,hscale⟩ := actual_uniform_holder_physical_radius_two hrho
    (Real.sqrt_pos.mpr hLambda) (inv_pos.mpr (Real.sqrt_pos.mpr hlam)) hK halpha hepsilon
  refine ⟨r,hr,hr1,?_⟩
  intro x₀ U hU hUb hclosed A hlo hhi hreg hdiv hhold x hx G hfreeze
  have hxU : x ∈ U := hclosed
    ((closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)) (ball_subset_closedBall hx))
  obtain ⟨hGn,hHn⟩ := actual_frozen_normalization_bounds_from_constants_two hU A
    (fun i j => (hreg i j).continuousOn) hlam hLambda hlo hhi hxU G hfreeze
  obtain ⟨hcb,hdev⟩ := hscale x₀ U hclosed A.a hhold x hx G hGn hHn hfreeze
  refine ⟨hGn,hHn,hcb,?_⟩
  intro f u hf hu
  obtain ⟨B,hBl,hBL,hBa,hB0,hBr,hBd,hBdev,hBw⟩ :=
    actual_given_holder_frozen_physical_unit_ball_two hU hUb A G x hfreeze hreg hdiv
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
