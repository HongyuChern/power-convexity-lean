import PowerConvexity.Calculus.MinkowskiActualCollarExhaustionTwo

/-! # Exhaustion from a cofinal set of genuine common truncations

It is enough to find arbitrarily small *common* truncation thicknesses whose
actual boundary has positive unperturbed modified spectrum for every parameter.
Neither positivity for every sufficiently small thickness nor a parameter-
independent lower bound for the perturbed spectral minimum is required.

The selected thickness is fixed before invoking the actual P119 deformation.
Its perturbation radius may depend on that thickness.  This theorem does not
construct the classical family or establish the remaining boundary premise.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_exhaustion_from_cofinal_truncation_boundary_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A)
    {R ρ L : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hcofinal : ∀ d : ℝ, 0 < d → ∃ ε : ℝ, 0 < ε ∧ ε < d ∧
      ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∀ t : I,
      (∀ x ∈ minkowskiDomain t A (ball 0 R),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t)) := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball hAn t
  have hcompact (t : I) : IsCompact (closure (minkowskiDomain t A (ball 0 R))) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hσ (t : I) (x : E) (hx : x ∈ minkowskiDomain t A (ball 0 R)) :
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
    have hproper : minkowskiDomain t A (ball 0 R) ≠ univ := by
      intro he
      apply (hcompact t).ne_univ
      simp only [he,closure_univ]
    have hfront : (frontier (minkowskiDomain t A (ball 0 R))).Nonempty :=
      nonempty_frontier_iff.mpr ⟨⟨x,hx⟩,hproper⟩
    have hnot : x ∉ frontier (minkowskiDomain t A (ball 0 R)) := by
      rw [(hU t).frontier_eq]
      exact fun hh => hh.2 hx
    have hd : 0 < infDist x (frontier (minkowskiDomain t A (ball 0 R))) :=
      (isClosed_frontier.notMem_iff_infDist_pos hfront).mp hnot
    obtain ⟨ε,hε,hεd,hboundary⟩ :=
      hcofinal (min ρ (infDist x (frontier (minkowskiDomain t A (ball 0 R))))) (lt_min hρ hd)
    have hερ : ε < ρ := hεd.trans_le (min_le_left _ _)
    have hεx : ε < infDist x (frontier (minkowskiDomain t A (ball 0 R))) :=
      hεd.trans_le (min_le_right _ _)
    obtain ⟨η,hη,hresult⟩ := minkowski_actual_deformation_from_actual_boundary_sigma_two
      μ hK hKi e hab hAo hA hAK hSmooth hR hρ hL hε hερ
      hballA hballB hAb hBb hu J hboundary
    have hzero : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (fun _ : E => 0) :=
      ⟨(quadraticSubmodule E).zero_mem,
        (pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).zero_mem⟩
    have he0 : quadraticL2Energy μ K (fun _ : E => 0) ≤ η := by
      simpa [quadraticL2Energy] using hη.le
    simpa only [add_zero] using
      (hresult t (fun _ => 0) hzero he0).1 x (subset_closure ⟨hx,hεx⟩)
  intro t
  refine ⟨hσ t,?_⟩
  apply strictConvexOn_power_of_modifiedSigmaTwo e (hU t)
    (minkowskiDomain_convex hA (convex_ball 0 R) t) ((hu t).1.of_le (by norm_num))
    (strictPshDirichlet_negative (hU t) (hcompact t) (hu t).continuous_closure
      ((hu t).1.of_le (by norm_num)) (hu t).2.2.2.2 e (fun j => Complex.I • e j)
      (hu t).2.2.1) (hu t).2.2.1 (hσ t)

theorem minkowski_actual_cofinal_boundary_implies_all_truncations_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A)
    {R ρ L : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hcofinal : ∀ d : ℝ, 0 < d → ∃ ε : ℝ, 0 < ε ∧ ε < d ∧
      ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∀ ε : ℝ, 0 < ε → ∀ t : I,
      ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  have hresult := minkowski_actual_exhaustion_from_cofinal_truncation_boundary_two
    μ hK hKi e hab hAo hA hAK hSmooth hR hρ hL hballA hballB hAb hBb hu J hcofinal
  intro ε hε t x hx
  have hU : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  exact (hresult t).1 x (distanceInteriorDomain_frontier_value hU hε x hx).1

end PowerConvexity
