import PowerConvexity.Calculus.MinkowskiZeroParameterFirstZeroTwo

/-! # A genuine common spectral margin on the actual truncations near the ball

The same epsilon and the same actual perturbation ball are used for every
parameter in a nontrivial interval. No boundary spectral premise is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_common_spectral_margin_near_ball_two
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
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ eta > 0, ∃ tau > 0, tau ≤ (1/2 : ℝ) ∧ ∃ kappa > 0,
      (∀ t : I, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy μ K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          u t x+q x < 0) ∧
      ∀ t : I, (t : ℝ) ≤ tau → ∀ q : E → ℝ,
        IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy μ K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          kappa ≤ modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
  obtain ⟨eta,heta,hnegative,hm,hm0,hnear,hfirst⟩ := minkowski_common_ball_actual_zero_initialization_two
    μ hQK hKi hA hconv hK hboundary e hab hR hrho hL heps hepsrho hballA hballB hAb hBb hu J
  let V : I → Set E := fun t => distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps
  let m : I → ℝ := fun t => actualQuadraticSpectralMinimumTwo μ K e eta (V t) (u t)
  let t0 : I := ⟨0,by norm_num⟩
  change 0 < m t0 at hm0
  change ∀ᶠ t : I in 𝓝 t0, m t0/2 ≤ m t at hnear
  obtain ⟨delta,hdelta,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let tau := min (delta/2) (1/2 : ℝ)
  have htau : 0 < tau := lt_min (by positivity) (by norm_num)
  have htau1 : tau ≤ (1/2 : ℝ) := min_le_right _ _
  refine ⟨eta,heta,tau,htau,htau1,m t0/2,half_pos hm0,hnegative,?_⟩
  intro t ht q hq hEq x hx
  have htδ : (t : ℝ) < delta := lt_of_le_of_lt (ht.trans (min_le_left _ _)) (by linarith)
  have htball : t ∈ ball t0 delta := by
    simpa only [mem_ball,Subtype.dist_eq,Real.dist_eq,t0,sub_zero,abs_of_nonneg t.property.1] using htδ
  have hnearT : m t0/2 ≤ m t := hsub htball
  have hgeo (s : I) := minkowski_distanceInterior_uniform_geometry hA isOpen_ball
    hconv (convex_ball 0 R) hrho heps hepsrho hballA hballB hAb hBb s
  have hU : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl : closure (V t) ⊆ minkowskiDomain t A (ball 0 R) := (hgeo t).2.2.2.2
  exact hnearT.trans (actualQuadraticSpectralMinimumTwo_le μ hQK hKi e
    (hgeo t).2.2.2.1 ⟨0,(hgeo t).2.2.1⟩
    (fun y hy => ((hu t).1.contDiffAt (hU.mem_nhds (hcl hy))).of_le (by norm_num))
    (fun y hy => (hu t).2.2.1 y (hcl hy)) heta.le
    (fun q hq hEq y hy => hnegative t q hq.1 hEq y hy) hx hq hEq)

end PowerConvexity
