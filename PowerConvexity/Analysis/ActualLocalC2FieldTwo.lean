import PowerConvexity.Analysis.ActualUniformPhysicalExpansionTwo
import PowerConvexity.Analysis.ActualUniformQuadraticJetCompatibilityTwo

/-! # A local actual C2 polynomial field for the original weak equation

No global source bound is assumed: an actual interior restriction supplies it.
The original frozen PDE becomes the pointwise PDE of the reconstructed field.
Its almost-everywhere identification with the weak function is a separate node.
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

theorem actual_local_C2_polynomial_field_two
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U) (hu : ActualScalarWeakEquationTwo A f u)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ R > 0,
      ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
      ∃ P : E → E → ℝ,
        (∀ x ∈ ball x₀ delta, IsQuadraticPolynomial (P x)) ∧
        ContDiffOn ℝ 2 (fun x => P x x) (ball x₀ delta) ∧
        (∀ x ∈ ball x₀ delta, fderiv ℝ (fun y => P y y) x = fderiv ℝ (P x) x) ∧
        (∀ x ∈ ball x₀ delta, realHessian (fun y => P y y) x = realHessian (P x) x) ∧
        (∀ x ∈ ball x₀ delta,
          (∑ i, ∑ j, A.a x i j*euclideanHessian (fun y => P y y) x i j) = -f x) ∧
        ∀ x ∈ ball x₀ delta, ball x R ⊆ U ∧ ∀ n : ℕ,
          (∫ y in ball x (R*theta^n), (u y-P x y)^2) ≤
            C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
  classical
  obtain ⟨rho,hrho,hclosed,K,hK,F,hF,hLip,hbound⟩ :=
    actual_C1_scalar_local_uniform_two hU hfC hx₀
  have hsub : ball x₀ rho ⊆ U := ball_subset_closedBall.trans hclosed
  let A₀ := A.restrict hsub
  have hf₀ := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hu₀ := actual_scalar_weak_restrict_ball_two hU hrho hclosed hu
  obtain ⟨delta,hd,hdelta,R,hR,C,hC,theta,htheta,hthetab,hdata⟩ :=
    actual_uniform_physical_quadratic_expansion_two isOpen_ball isBounded_ball A₀
      (fun x hx => hpos x (hsub hx)) (fun i j => (hreg i j).mono hsub)
      (fun x hx j => hdiv x (hsub hx) j) hf₀ (hfC.mono hsub) hK hF
      (fun x hx y hy => hLip x (ball_subset_closedBall hx) y (ball_subset_closedBall hy))
      (fun x hx => hbound x (ball_subset_closedBall hx)) hu₀ (mem_ball_self hrho)
  have hex : ∀ x : E, ∃ p : E → ℝ, x ∈ ball x₀ delta →
      IsQuadraticPolynomial p ∧
      (∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) = -f x ∧
      ∀ n : ℕ, (∫ y in ball x (R*theta^n), (u y-p y)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
    intro x
    by_cases hx : x ∈ ball x₀ delta
    · obtain ⟨p,hp,hpde,herr⟩ := (hdata x hx).2
      exact ⟨p,fun _ => ⟨hp,hpde,herr⟩⟩
    · exact ⟨fun _ => 0,fun h => (hx h).elim⟩
  choose P hP using hex
  have hballs : ∀ x ∈ ball x₀ delta, ball x R ⊆ U := fun x hx => (hdata x hx).1.trans hsub
  have hC2 := actual_polynomial_field_C2_of_uniform_L2_expansion_two isOpen_ball
    (MemW1p.someWitness hu.1).memLp P (fun x hx => (hP x hx).1) hR htheta
    (by linarith : theta < 1) hC hballs (fun x hx => (hP x hx).2.2)
  refine ⟨delta,hd,hdelta.trans hsub,R,hR,C,hC,theta,htheta,hthetab,P,
    (fun x hx => (hP x hx).1),hC2.1,hC2.2.1,hC2.2.2,?_,?_⟩
  · intro x hx
    simpa only [euclideanHessian,hC2.2.2 x hx] using (hP x hx).2.1
  · intro x hx
    exact ⟨hballs x hx,(hP x hx).2.2⟩

end PowerConvexity
