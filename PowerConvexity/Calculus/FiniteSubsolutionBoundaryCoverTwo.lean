import PowerConvexity.Calculus.MinkowskiLocalSubsolutionTwo

/-! # A finite covering by genuine local strict subsolutions

The finite family is preparation for a global construction. A finite cover
alone is not a single smooth global subsolution.
-/
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

def BallSubsolutionDataTwo (a b : Fin 2 → E) (U : Set E) (c : E) (r : ℝ) (w : E → ℝ) : Prop :=
  0 < r ∧ ContDiffOn ℝ 4 w (ball c r) ∧
    (∀ z ∈ ball c r, z ∈ U ↔ w z < 0) ∧
    (∀ z ∈ ball c r ∩ frontier U, w z = 0) ∧
    (∀ z ∈ ball c r, (complexHessian a b w z).PosDef ∧
      (1 : ℂ) < (complexHessian a b w z).det)

theorem exists_finite_subsolution_boundary_cover_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (frontier U))
    (hlocal : ∀ x ∈ frontier U, ∃ r : ℝ, ∃ w : E → ℝ, BallSubsolutionDataTwo a b U x r w) :
    ∃ r : frontier U → ℝ, ∃ w : frontier U → E → ℝ, ∃ S : Finset (frontier U),
      (∀ p : frontier U, BallSubsolutionDataTwo a b U p (r p) (w p)) ∧
      frontier U ⊆ ⋃ p ∈ S, ball (p : E) (r p/4) := by
  classical
  choose r w hdata using (fun p : frontier U => hlocal p p.property)
  have hcover : frontier U ⊆ ⋃ p : frontier U, ball (p : E) (r p/4) := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x,hx⟩,mem_ball_self ?_⟩
    exact div_pos (hdata ⟨x,hx⟩).1 (by norm_num)
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover (fun p : frontier U => ball (p : E) (r p/4))
    (fun _ => isOpen_ball) hcover
  exact ⟨r,w,S,hdata,hS⟩

end General

variable [InnerProductSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_finite_subsolution_boundary_cover_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ r : frontier V → ℝ, ∃ w : frontier V → E → ℝ, ∃ S : Finset (frontier V),
      (∀ p : frontier V, BallSubsolutionDataTwo e (fun j => Complex.I • e j) V p (r p) (w p)) ∧
      frontier V ⊆ ⋃ p ∈ S, ball (p : E) (r p/4) := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hKV : IsCompact (closure V) := by
    obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
    have hUb (x : E) (hx : x ∈ U) : ‖x‖ ≤ max L R :=
      (hL x (subset_closure hx)).trans (le_max_left _ _)
    have hBb (x : E) (hx : x ∈ ball (0 : E) R) : ‖x‖ ≤ max L R := by
      have hh : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
      exact hh.le.trans (le_max_right _ _)
    exact minkowskiDomain_isCompact_closure hUb hBb ht.le ht1.le
  apply exists_finite_subsolution_boundary_cover_two e (fun j => Complex.I • e j)
    (hKV.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  intro x hx
  obtain ⟨w,r,hr,hw,hwx,hDw,hreg,hdef,hzero,hpos⟩ :=
    classicalDirichlet_minkowski_exists_ball_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hx
  exact ⟨r,w,hr,hreg,hdef,hzero,hpos⟩

end PowerConvexity
