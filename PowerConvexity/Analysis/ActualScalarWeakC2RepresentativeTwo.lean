import PowerConvexity.Analysis.ActualLocalC2FieldTwo
import PowerConvexity.Analysis.ActualQuadraticAverageIdentificationTwo
import PowerConvexity.Analysis.ActualWeakDomainRepresentativeTwo
import CHS.Calculus.HessianLocality

/-! # Actual C2 interior representatives for the variable-coefficient scalar equation

The representative is constructed from the actual weak solution, identified
almost everywhere, and glued on the original open set. The weak equation and
pointwise non-divergence equation both hold for that same representative.
No classical boundary value or boundary C2 jet is asserted here.
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

theorem actual_scalar_weak_local_C2_representative_two
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U) (hu : ActualScalarWeakEquationTwo A f u)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ v : E → ℝ,
      v =ᵐ[volume.restrict (ball x₀ delta)] u ∧
      ContDiffOn ℝ 2 v (ball x₀ delta) ∧
      ∀ x ∈ ball x₀ delta,
        (∑ i, ∑ j, A.a x i j*euclideanHessian v x i j) = -f x := by
  obtain ⟨delta,hd,hsub,R,hR,C,hC,theta,htheta,hthetab,P,hP,hvC,hD,hH,hPDE,herror⟩ :=
    actual_local_C2_polynomial_field_two hU A hpos hreg hdiv hf hfC hu hx₀
  have hAE := actual_polynomial_field_ae_eq_of_uniform_L2_two isOpen_ball isBounded_ball
    (ball_subset_closedBall.trans hsub) (MemW1p.someWitness hu.1).memLp P hP
    hR htheta (by linarith : theta < 1) hC
    (fun x hx => (herror x hx).1) (fun x hx => (herror x hx).2)
  exact ⟨delta,hd,hsub,(fun x => P x x),hAE,hvC,hPDE⟩

theorem actual_scalar_weak_C2_interior_representative_two
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U) (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ v : E → ℝ, v =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ 2 v U ∧
      ActualScalarWeakEquationTwo A f v ∧
      ∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian v x i j) = -f x := by
  have hlocal := fun x hx => actual_scalar_weak_local_C2_representative_two
    hU A hpos hreg hdiv hf hfC hu (x₀ := x) hx
  obtain ⟨v,hvC,hvu⟩ := actual_continuous_representative_of_local_two (u := u) (U := U) (by
    intro x hx
    obtain ⟨delta,hd,hsub,w,hwu,hwC,hwPDE⟩ := hlocal x hx
    exact ⟨ball x delta,w,isOpen_ball,mem_ball_self hd,ball_subset_closedBall.trans hsub,
      hwC.continuousOn,hwu⟩)
  have hlocmatch (x : E) (hx : x ∈ U) :
      ∃ w : E → ℝ, v =ᶠ[𝓝 x] w ∧ ContDiffAt ℝ 2 w x ∧
        (∑ i, ∑ j, A.a x i j*euclideanHessian w x i j) = -f x := by
    obtain ⟨delta,hd,hsub,w,hwu,hwC,hwPDE⟩ := hlocal x hx
    have hball := ball_subset_closedBall.trans hsub
    have hvuB : v =ᵐ[volume.restrict (ball x delta)] u :=
      ae_restrict_of_ae_restrict_of_subset hball hvu
    have hvw : v =ᵐ[volume.restrict (ball x delta)] w := hvuB.trans hwu.symm
    have he := Measure.eqOn_open_of_ae_eq hvw isOpen_ball (hvC.mono hball) hwC.continuousOn
    have hxB : x ∈ ball x delta := mem_ball_self hd
    refine ⟨w,?_,hwC.contDiffAt (isOpen_ball.mem_nhds hxB),hwPDE x hxB⟩
    filter_upwards [ball_mem_nhds x hd] with y hy
    exact he hy
  have hv2 : ContDiffOn ℝ 2 v U := by
    intro x hx
    obtain ⟨w,he,hw,_⟩ := hlocmatch x hx
    exact (hw.congr_of_eventuallyEq he).contDiffWithinAt
  refine ⟨v,hvu,hv2,actual_scalar_weak_congr_ae_two hvu.symm hu,?_⟩
  intro x hx
  obtain ⟨w,he,hw,hPDE⟩ := hlocmatch x hx
  simpa only [euclideanHessian,realHessian_eq_of_eventuallyEq he] using hPDE

end PowerConvexity
