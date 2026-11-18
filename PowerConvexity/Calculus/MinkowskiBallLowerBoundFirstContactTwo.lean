import PowerConvexity.Calculus.MinkowskiPositiveParameterDeformationTwo

/-! # The exact one-sided lower-bound input on P84's constructed common ball

The common radius and m(0)>0 are constructed. The one-sided lower bound is
explicitly conditional and is not derived from joint C0 value continuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_common_ball_first_zero_from_zero_lower_bound_two
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
       0 < m t0 ∧
       ((∀ᶠ t : I in 𝓝 t0, m t0/2 ≤ m t) → m ⟨1,by norm_num⟩ ≤ 0 →
         ∃ s : I, 0 < (s : ℝ) ∧ m s = 0 ∧
           ∀ t : I, (t : ℝ) < (s : ℝ) → 0 < m t)) := by
  obtain ⟨eta,heta,hnegative,hm0,hm⟩ :=
    minkowski_family_exists_common_radius_ball_minimum_positive_two
      μ hQK hKi hA hconv hK hboundary e hab hR hrho hL heps hepsrho
      hballA hballB hAb hBb hu J
  refine ⟨eta,heta,hnegative,hm0,?_⟩
  intro hbound h1
  apply unitInterval_exists_first_zero_of_eventually_positive hm ?_ h1
  filter_upwards [hbound] with t ht
  exact (half_pos hm0).trans_le ht

end PowerConvexity
