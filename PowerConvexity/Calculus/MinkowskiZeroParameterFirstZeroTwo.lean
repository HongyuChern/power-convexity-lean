import PowerConvexity.Calculus.MinkowskiAllParameterActualMinimumTwo
import PowerConvexity.Calculus.MinkowskiBallLowerBoundFirstContactTwo

/-! # The actual common perturbation ball initializes the first-zero argument.
The zero-side lower bound is proved for the same actual minimum, radius and
truncation, without a new analytic premise. Classical existence and the
boundary spectral collar remain separate obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_common_ball_actual_zero_initialization_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ eta : ℝ, 0 < eta ∧
      (∀ t : I, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy μ K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          u t x+q x < 0) ∧
      (let m : I → ℝ := fun t => actualQuadraticSpectralMinimumTwo μ K e eta
          (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps) (u t)
       let t0 : I := ⟨0,by norm_num⟩
       Continuous m ∧ 0 < m t0 ∧
       (∀ᶠ t : I in 𝓝 t0, m t0/2 ≤ m t) ∧
       (m ⟨1,by norm_num⟩ ≤ 0 → ∃ s : I, 0 < (s : ℝ) ∧ m s = 0 ∧
         ∀ t : I, (t : ℝ) < (s : ℝ) → 0 < m t)) := by
  obtain ⟨eta,heta,hnegative,hm0,hmpos⟩ :=
    minkowski_family_exists_common_radius_ball_minimum_positive_two
      μ hQK hKi hA hconv hK hboundary e hab hR hrho hL heps hepsrho
      hballA hballB hAb hBb hu J
  let m : I → ℝ := fun t => actualQuadraticSpectralMinimumTwo μ K e eta
    (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps) (u t)
  let t0 : I := ⟨0,by norm_num⟩
  have hm : Continuous m := minkowski_family_quadratic_minimum_continuous_two
    μ hQK hKi hA hconv hK hboundary e hab hR hrho hL heps hepsrho heta.le
    hballA hballB hAb hBb hu J (fun t q hq hEq x hx => hnegative t q hq.1 hEq x hx)
  have hmzero : 0 < m t0 := hm0
  have hnear : ∀ᶠ t : I in 𝓝 t0, m t0/2 ≤ m t := by
    have hn := hm.continuousAt.tendsto.eventually
      (lt_mem_nhds (by linarith only [hmzero] : m t0/2 < m t0))
    exact hn.mono (fun t ht => ht.le)
  refine ⟨eta,heta,hnegative,hm,hmzero,hnear,?_⟩
  intro h1
  apply unitInterval_exists_first_zero_of_eventually_positive
    (fun s _ => hm.continuousAt) ?_ h1
  filter_upwards [hnear] with t ht
  exact (half_pos hmzero).trans_le ht

end PowerConvexity
