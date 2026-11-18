import PowerConvexity.Analysis.ActualScalarWeakEnergyTwo

/-! # Localization of the actual scalar weak equation.
The scalar source and all Sobolev test functions are retained. The proof
uses zero extension of the actual local test, including its weak gradient,
and proves equality of the scalar source integrals on the two domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_weak_congr_ae_two {U : Set F}
    {A : EllipticCoeff (2+2) U} {f u v : F → ℝ}
    (huv : u =ᵐ[volume.restrict U] v)
    (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo A f v := by
  refine ⟨(MemW1pWitness.ofAeEq huv (MemW1p.someWitness hu.1)).memW1p,?_⟩
  intro vw phi hp pw
  let uw : MemW1pWitness 2 u U := MemW1pWitness.ofAeEq huv.symm vw
  exact hu.2 uw phi hp pw

theorem actual_scalar_weak_restrict_ball_two {U : Set F}
    (hU : IsOpen U) {c : F} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff (2+2) U} {f u : F → ℝ}
    (hsub : closedBall c r ⊆ U) (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hsub)) f u := by
  let huw := MemW1p.someWitness hu.1
  refine ⟨(huw.restrict isOpen_ball (ball_subset_closedBall.trans hsub)).memW1p,?_⟩
  intro uw phi hp pw
  have hpbig : MemH01 ((ball c r).indicator phi) U :=
    memH01_indicator_ball_of_closedBall_subset hU hr hsub hp
  let pwbig := ballIndicatorWitnessOn hU hp pw
  have hbig : bilinFormOfCoeff A huw pwbig =
      ∫ x in U, f x*((ball c r).indicator phi x) := hu.2 huw _ hpbig pwbig
  calc
    bilinFormOfCoeff (A.restrict (ball_subset_closedBall.trans hsub)) uw pw
        = bilinFormOfCoeff (A.restrict (ball_subset_closedBall.trans hsub))
            (huw.restrict isOpen_ball (ball_subset_closedBall.trans hsub)) pw :=
      bilinFormOfCoeff_eq_left isOpen_ball _ uw _ pw
    _ = bilinFormOfCoeff A huw (ballIndicatorWitnessOn hU hp pw) :=
      bilinForm_ball_restrict_eq_zeroExtend hU A hr hsub huw hp pw
    _ = ∫ x in U, f x*((ball c r).indicator phi x) := hbig
    _ = ∫ x in U, (ball c r).indicator (fun y => f y*phi y) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ ball c r <;> simp [hx])
    _ = ∫ x in ball c r, f x*phi x := by
      rw [integral_indicator measurableSet_ball,Measure.restrict_restrict measurableSet_ball]
      rw [inter_eq_left.mpr (ball_subset_closedBall.trans hsub)]

theorem actual_dirichlet_scalar_restrict_ball_two {U : Set F}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (A : EllipticCoeff (2+2) U)
    {f u : F → ℝ}
    (hu : IsWeakSolution ⟨U,hU,hUb,A,(fun phi => ∫ x in U, f x*phi x)⟩ u)
    {c : F} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ U) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hsub)) f u :=
  actual_scalar_weak_restrict_ball_two hU hr hsub
    (actual_scalar_weak_equation_of_dirichlet_two hU hUb A hu)

end PowerConvexity
