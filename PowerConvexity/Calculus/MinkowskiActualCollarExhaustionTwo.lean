import PowerConvexity.Calculus.MinkowskiActualDeformationFromCollarTwo
import PowerConvexity.Calculus.MinkowskiDeformationExhaustionTwo

/-! # Exhaustion using the closed zero-parameter interface

The former exhaustion theorem required a separate local boundary Hessian
upper bound at every parameter.  The actual P119 call no longer requires that
input.  Here every chosen distance truncation and its perturbation ball are
kept fixed while applying P119; only then is the truncation exhausted.

Classical solvability and actual boundary spectral positivity remain explicit
inputs.  This file does not prove either input from the original geometry.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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

theorem minkowski_actual_exhaustion_from_small_truncation_boundary_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A)
    {R ρ L δ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hboundary : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ t : I,
      ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
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
    let ε := min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) / 2
    have hm : 0 < min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) :=
      lt_min (lt_min hρ hδ) hd
    have hε : 0 < ε := half_pos hm
    have hεm : ε < min (min ρ δ) (infDist x (frontier (minkowskiDomain t A (ball 0 R)))) :=
      half_lt_self hm
    have hερ : ε < ρ := hεm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hεδ : ε < δ := hεm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hεd : ε < infDist x (frontier (minkowskiDomain t A (ball 0 R))) :=
      hεm.trans_le (min_le_right _ _)
    obtain ⟨η,hη,hresult⟩ := minkowski_actual_deformation_from_actual_boundary_sigma_two
      μ hK hKi e hab hAo hA hAK hSmooth hR hρ hL hε hερ
      hballA hballB hAb hBb hu J (hboundary ε hε hεδ)
    have hzero : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (fun _ : E => 0) :=
      ⟨(quadraticSubmodule E).zero_mem,
        (pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).zero_mem⟩
    have he0 : quadraticL2Energy μ K (fun _ : E => 0) ≤ η := by
      simpa [quadraticL2Energy] using hη.le
    simpa only [add_zero] using
      (hresult t (fun _ => 0) hzero he0).1 x (subset_closure ⟨hx,hεd⟩)
  intro t
  refine ⟨hσ t,?_⟩
  apply strictConvexOn_power_of_modifiedSigmaTwo e (hU t)
    (minkowskiDomain_convex hA (convex_ball 0 R) t) ((hu t).1.of_le (by norm_num))
    (strictPshDirichlet_negative (hU t) (hcompact t) (hu t).continuous_closure
      ((hu t).1.of_le (by norm_num)) (hu t).2.2.2.2 e (fun j => Complex.I • e j)
      (hu t).2.2.1) (hu t).2.2.1 (hσ t)

end PowerConvexity
