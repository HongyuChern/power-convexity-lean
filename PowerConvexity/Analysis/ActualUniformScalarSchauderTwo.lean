import PowerConvexity.Analysis.ActualUniformHolderPhysicalExpansionTwo
import PowerConvexity.Analysis.ActualFamilyQuadraticHolderTwo
import PowerConvexity.Analysis.ActualFamilyQuadraticBoundTwo

/-! # Actual quadratic approximation uniform over Holder coefficient families

Every constant is selected before the domain, coefficient, source, solution,
centre and normalizing map. No quantitative coefficient C1 bound occurs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_scalar_C2_holder_interior_two
    {rho lam Lambda Ka Kf F N₀ alpha : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hN₀ : 0 ≤ N₀)
    (halpha : 0 < alpha) :
    ∃ delta > 0, delta ≤ rho/4 ∧ ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ x₀ : E, ∀ U : Set E,
      IsOpen U → Bornology.IsBounded U → closedBall x₀ rho ⊆ U →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, (A.a x).PosDef) →
      (∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U) →
      (∀ y ∈ U, ∀ j,
        (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ closedBall x₀ rho, ∀ y ∈ closedBall x₀ rho,
        ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤
          Ka*‖x-y‖^alpha) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict U) → ContDiffOn ℝ 1 f U →
      (∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha) →
      (∀ x ∈ U, |f x| ≤ F) → ContinuousOn u U → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u U, ‖uw.memLp.toLp u‖ ≤ N₀ →
      ContDiffOn ℝ 2 u (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta,
        |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ M ∧ ‖realHessian u x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian u x-realHessian u y‖ ≤ M*‖x-y‖^beta := by
  classical
  obtain ⟨R,hR,C,hC,theta,htheta,hthetab,happrox⟩ :=
    actual_uniform_holder_physical_quadratic_expansion_two hrho hlam hLambda
      hKa hKf hF hN₀ halpha
  have htheta1 : theta < 1 := by linarith
  obtain ⟨beta,hbeta,hbeta1,H,hH,hholder⟩ :=
    actual_family_quadratic_Hessian_holder_two hR htheta htheta1 hC
  obtain ⟨T,hT,hjetbound⟩ := actual_family_quadratic_absolute_jet_bound_two hR hC hN₀
  let delta := min (rho/8) (R/8)
  have hd : 0 < delta := lt_min (by positivity) (by positivity)
  have hdelta : delta ≤ rho/4 := (min_le_left _ _).trans (by linarith)
  have hdR : delta ≤ R/8 := min_le_right _ _
  let M := max H T
  have hM : 0 ≤ M := hT.trans (le_max_right _ _)
  refine ⟨delta,hd,hdelta,beta,hbeta,hbeta1,M,hM,?_⟩
  intro x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold f u hf hfC hLip hbound huC hu uw hun
  let V := ball x₀ (rho/4)
  have hVU : V ⊆ U := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith : rho/4 ≤ rho))).trans hclosed
  have hdata := happrox x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold
    f u hf hfC hLip hbound hu uw hun
  have hex : ∀ x : E, ∃ p : E → ℝ, x ∈ V →
      IsQuadraticPolynomial p ∧ ∀ n : ℕ,
      (∫ y in ball x (R*theta^n), (u y-p y)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
    intro x
    by_cases hx : x ∈ V
    · obtain ⟨p,hp,hpde,herr⟩ := (hdata x hx).2
      exact ⟨p,fun _ => ⟨hp,herr⟩⟩
    · exact ⟨fun _ => 0,fun h => (hx h).elim⟩
  choose P hP using hex
  have hballs : ∀ x ∈ V, ball x R ⊆ U := fun x hx => (hdata x hx).1
  have herr := fun x hx => (hP x hx).2
  have hfield := actual_continuous_polynomial_field_jets_identify_two isOpen_ball isBounded_ball
    hVU uw.memLp (huC.mono hVU) P (fun x hx => (hP x hx).1)
    hR htheta htheta1 hC hballs herr
  have hsub : ball x₀ delta ⊆ V := ball_subset_ball hdelta
  refine ⟨hfield.1.mono hsub,?_,?_⟩
  · intro x hx
    have hxV := hsub hx
    obtain ⟨hv,hD,hess⟩ := hfield.2 x hxV
    have he : (∫ y in ball x R, (u y-P x y)^2) ≤ C*R^8 := by
      simpa only [pow_zero,one_pow,mul_one] using herr x hxV 0
    obtain ⟨hb0,hb1,hb2⟩ := hjetbound U u uw.memLp hun x (P x)
      (hP x hxV).1 (hballs x hxV) he
    rw [hv,hD,hess]
    exact ⟨hb0.trans (le_max_right _ _),hb1.trans (le_max_right _ _),hb2.trans (le_max_right _ _)⟩
  · intro x hx y hy
    have hnear : dist x y < R/2 := by
      have hx0 : dist x x₀ < delta := hx
      have hy0 : dist y x₀ < delta := hy
      have ht := dist_triangle x x₀ y
      rw [dist_comm x₀ y] at ht
      linarith
    have hb := hholder U V u uw.memLp P (fun x hx => (hP x hx).1)
      hballs herr x (hsub hx) y (hsub hy) hnear
    rw [(hfield.2 x (hsub hx)).2.2,(hfield.2 y (hsub hy)).2.2]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))

end PowerConvexity
