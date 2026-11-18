import PowerConvexity.Calculus.RegularLocalSubsolutionCoverTwo

/-! # C6 local subsolutions from the unchanged smooth-boundary hypotheses

Only finite regularity is selected on each actual neighborhood. In particular,
ContDiffAt infinity at one point is not treated as a fixed smooth neighborhood.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

def RegularBallSubsolutionC6DataTwo (a b : Fin 2 → E) (U : Set E)
    (c : E) (r : ℝ) (w : E → ℝ) : Prop :=
  (0 < r ∧ ContDiffOn ℝ 6 w (ball c r) ∧
    (∀ z ∈ ball c r, z ∈ U ↔ w z < 0) ∧
    (∀ z ∈ ball c r ∩ frontier U, w z = 0) ∧
    (∀ z ∈ ball c r, (complexHessian a b w z).PosDef ∧
      (1 : ℂ) < (complexHessian a b w z).det)) ∧
    ∀ z ∈ ball c r, fderiv ℝ w z ≠ 0

theorem RegularBallSubsolutionC6DataTwo.toC4
    {a b : Fin 2 → E} {U : Set E} {c : E} {r : ℝ} {w : E → ℝ}
    (h : RegularBallSubsolutionC6DataTwo a b U c r w) :
    RegularBallSubsolutionDataTwo a b U c r w :=
  ⟨⟨h.1.1,h.1.2.1.of_le (by norm_num),h.1.2.2⟩,h.2⟩

theorem exists_finite_regular_C6_subsolution_boundary_cover_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (frontier U))
    (hlocal : ∀ x ∈ frontier U, ∃ r : ℝ, ∃ w : E → ℝ,
      RegularBallSubsolutionC6DataTwo a b U x r w) :
    ∃ r : frontier U → ℝ, ∃ w : frontier U → E → ℝ, ∃ S : Finset (frontier U),
      (∀ p : frontier U, RegularBallSubsolutionC6DataTwo a b U p (r p) (w p)) ∧
      frontier U ⊆ ⋃ p ∈ S, ball (p : E) (r p/4) := by
  classical
  choose r w hdata using (fun p : frontier U => hlocal p p.property)
  have hcover : frontier U ⊆ ⋃ p : frontier U, ball (p : E) (r p/4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (div_pos (hdata ⟨x,hx⟩).1.1 (by norm_num))⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover (fun p : frontier U => ball (p : E) (r p/4))
    (fun _ => isOpen_ball) hcover
  exact ⟨r,w,S,hdata,hS⟩

end General

variable [InnerProductSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_exists_regular_C6_ball_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ r : ℝ, ∃ w : E → ℝ,
      RegularBallSubsolutionC6DataTwo e (fun j => Complex.I • e j)
        (minkowskiDomain t U (ball (0 : E) R)) y r w := by
  obtain ⟨w,hw,hwy,hDw,hnear⟩ := classicalDirichlet_minkowski_exists_local_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hy
  have hw6 : ContDiffAt ℝ 6 w y := (contDiffAt_infty.mp hw) 6
  have hD : ContinuousAt (fun z => fderiv ℝ w z) y :=
    (hw6.fderiv_right (m := 5) (by norm_num)).continuousAt
  have hnb := hnear.and ((hw6.eventually (by norm_num)).and (hD.eventually_ne hDw))
  obtain ⟨r,hr,hrP⟩ := Metric.eventually_nhds_iff.mp hnb
  have hP (z : E) (hz : z ∈ ball y r) := hrP (show dist z y < r from hz)
  refine ⟨r,w,⟨hr,?_,?_,?_,?_⟩,?_⟩
  · intro z hz
    exact (hP z hz).2.1.contDiffWithinAt
  · intro z hz
    exact (hP z hz).1.1
  · intro z hz
    exact (hP z hz.1).1.2.2.1 hz.2
  · intro z hz
    exact (hP z hz).1.2.2.2
  · intro z hz
    exact (hP z hz).2.2

end PowerConvexity
