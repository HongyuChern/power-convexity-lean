import PowerConvexity.Analysis.ActualUniformHolderScalarExpansionTwo
import PowerConvexity.Analysis.ActualUniformPhysicalExpansionTwo

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

theorem actual_uniform_holder_physical_quadratic_expansion_two
    {rho lam Lambda Ka Kf F N₀ alpha : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hN₀ : 0 ≤ N₀)
    (halpha : 0 < alpha) :
    ∃ R > 0, ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
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
      (∀ x ∈ U, |f x| ≤ F) → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u U, ‖uw.memLp.toLp u‖ ≤ N₀ →
      ∀ x ∈ ball x₀ (rho/4), ball x R ⊆ U ∧
        ∃ P : E → ℝ, IsQuadraticPolynomial P ∧
          (∑ i, ∑ j, A.a x i j*euclideanHessian P x i j) = -f x ∧
          ∀ n : ℕ,
            (∫ y in ball x (R*theta^n), (u y-P y)^2) ≤
              C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
  obtain ⟨r,hr,hr1,C,hC,theta,htheta,hthetab,happrox⟩ :=
    actual_uniform_holder_local_scalar_quadratic_expansion_two hrho hlam hLambda
      hKa hKf hF hN₀ halpha
  let B := max (1 : ℝ) (Real.sqrt lam)⁻¹
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let R := r/B
  have hR : 0 < R := div_pos hr hB
  obtain ⟨J,hJ,hJac⟩ := actual_linear_forward_jacobians_uniform_two (Real.sqrt Lambda)
  let D := J*r^4*C/R^8
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨R,hR,D,hD,theta,htheta,hthetab,?_⟩
  intro x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold f u hf hfC hLip hbound hu uw hun x hx
  have hdata := happrox x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold
    f u hf hfC hLip hbound hu uw hun
  obtain ⟨G,hfreeze,hclosed,hGn,hHn,p,hp,htrace,herror⟩ := hdata x hx
  have hGB : ‖G.symm.toContinuousLinearMap‖ ≤ B := hHn.trans (le_max_right _ _)
  have hsub : ball x R ⊆ U := by
    simpa only [G.apply_symm_apply] using
      actual_physical_ball_subset_of_inverse_norm_two G (G.symm x) hr hB hGB hclosed
  let P := actualPhysicalQuadraticTwo G (G.symm x) r p
  have hP := actual_physical_quadratic_isQuadratic_two G (G.symm x) r hp
  have hpm : MemLp P 2 (volume.restrict U) :=
    continuous_memLp_two_of_subset_compact hUb.isCompact_closure subset_closure
      (IsQuadraticPolynomial_contDiff hP 0).continuous
  have hum := (MemW1p.someWitness hu.1).memLp
  have hI : IntegrableOn (fun y => (u y-P y)^2) U := by
    change Integrable (fun y => (u y-P y)^2) (volume.restrict U)
    exact (hum.sub hpm).integrable_sq
  refine ⟨hsub,P,hP,?_,?_⟩
  · simpa only [G.apply_symm_apply] using
      actual_physical_quadratic_frozen_equation_two G (G.symm x) hr hfreeze hp (htrace 0)
  · intro n
    have hs1 : theta^n ≤ 1 := pow_le_one₀ htheta.le (by linarith : theta ≤ 1)
    have hphys := actual_physical_ball_integral_bound_two hI (fun y => sq_nonneg (u y-P y))
      G (G.symm x) hr (pow_pos htheta n) hs1 hB hGB (hJac G hGn) hclosed
    have hn : (∫ y in ball x (R*theta^n), (u y-P y)^2) ≤
        J*r^4*(∫ z in ball (0 : E) (theta^n), (u (G (G.symm x+r • z))-p z)^2) := by
      simpa only [G.apply_symm_apply,P,actual_physical_quadratic_pullback_two G (G.symm x) hr p] using hphys
    calc
      _ ≤ J*r^4*(C*((1/2 : ℝ)^n)^2*(theta^n)^8) :=
        hn.trans (mul_le_mul_of_nonneg_left (herror n) (mul_nonneg hJ.le (pow_nonneg hr.le 4)))
      _ = D*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
        dsimp [D]
        field_simp
        <;> ring


end PowerConvexity
