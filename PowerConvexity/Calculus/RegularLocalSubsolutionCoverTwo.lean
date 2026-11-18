import PowerConvexity.Calculus.FiniteSubsolutionBoundaryCoverTwo

/-! # Retaining a regular gradient on each local subsolution ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

def RegularBallSubsolutionDataTwo (a b : Fin 2 → E) (U : Set E)
    (c : E) (r : ℝ) (w : E → ℝ) : Prop :=
  BallSubsolutionDataTwo a b U c r w ∧ ∀ z ∈ ball c r, fderiv ℝ w z ≠ 0

theorem local_subsolution_shrink_regular_two
    (a b : Fin 2 → E) {U : Set E} {x : E} {w : E → ℝ} {r : ℝ}
    (hdata : BallSubsolutionDataTwo a b U x r w) (hDw : fderiv ℝ w x ≠ 0) :
    ∃ s : ℝ, RegularBallSubsolutionDataTwo a b U x s w := by
  have hw : ContDiffAt ℝ 4 w x := hdata.2.1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hdata.1))
  have hD : ContinuousAt (fun y => fderiv ℝ w y) x :=
    (hw.fderiv_right (m := 3) (by norm_num)).continuousAt
  obtain ⟨d,hd,hdN⟩ := Metric.eventually_nhds_iff.mp (hD.eventually_ne hDw)
  let s := min r d
  have hs : 0 < s := lt_min hdata.1 hd
  have hsr : ball x s ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  refine ⟨s,⟨hs,hdata.2.1.mono hsr,
    (fun z hz => hdata.2.2.1 z (hsr hz)),
    (fun z hz => hdata.2.2.2.1 z ⟨hsr hz.1,hz.2⟩),
    (fun z hz => hdata.2.2.2.2 z (hsr hz))⟩,?_⟩
  intro z hz
  exact hdN ((mem_ball.mp hz).trans_le (min_le_right _ _))

theorem exists_finite_regular_subsolution_boundary_cover_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (frontier U))
    (hlocal : ∀ x ∈ frontier U, ∃ r : ℝ, ∃ w : E → ℝ, RegularBallSubsolutionDataTwo a b U x r w) :
    ∃ r : frontier U → ℝ, ∃ w : frontier U → E → ℝ, ∃ S : Finset (frontier U),
      (∀ p : frontier U, RegularBallSubsolutionDataTwo a b U p (r p) (w p)) ∧
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

theorem classicalDirichlet_minkowski_exists_regular_ball_subsolution_two
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
      RegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
        (minkowskiDomain t U (ball (0 : E) R)) y r w := by
  obtain ⟨w,r,hr,hw,hwy,hDw,hreg,hdef,hzero,hpos⟩ :=
    classicalDirichlet_minkowski_exists_ball_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hy
  obtain ⟨s,hs⟩ := local_subsolution_shrink_regular_two e (fun j => Complex.I • e j)
    ⟨hr,hreg,hdef,hzero,hpos⟩ hDw
  exact ⟨s,w,hs⟩

end PowerConvexity
