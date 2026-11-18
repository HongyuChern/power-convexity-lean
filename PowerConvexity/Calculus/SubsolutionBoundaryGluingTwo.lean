import PowerConvexity.Calculus.FiniteSubsolutionBoundaryCoverTwo
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # A global C4 boundary sign function from actual local subsolutions

The finite bump sum has the correct local negative side and zero boundary.
Regularity of its gradient and Levi positivity are separate next obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_C4_boundary_sign_function_of_local_subsolutions_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (frontier U))
    (hlocal : ∀ x ∈ frontier U, ∃ r : ℝ, ∃ w : E → ℝ, BallSubsolutionDataTwo a b U x r w) :
    ∃ F : E → ℝ, ContDiff ℝ 4 F ∧
      (∀ x ∈ frontier U, F x = 0) ∧
      (∀ x ∈ U, F x ≤ 0) ∧ (∀ x ∉ U, 0 ≤ F x) ∧
      ∃ W : Set E, IsOpen W ∧ frontier U ⊆ W ∧
        ∀ x ∈ W, x ∈ U ↔ F x < 0 := by
  classical
  obtain ⟨r,w,S,hdata,hcover⟩ := exists_finite_subsolution_boundary_cover_two a b hK hlocal
  let B (p : frontier U) : ContDiffBump (p : E) :=
    ⟨r p/4,r p/2,div_pos (hdata p).1 (by norm_num),by linarith [(hdata p).1]⟩
  let F : E → ℝ := fun x => ∑ p ∈ S, B p x*w p x
  let W : Set E := ⋃ p ∈ S, ball (p : E) (r p/4)
  have hball (p : frontier U) {x : E} (hBx : B p x ≠ 0) : x ∈ ball (p : E) (r p) := by
    have hs : x ∈ ball (p : E) (r p/2) := by
      change x ∈ ball (p : E) (B p).rOut
      rw [← (B p).support_eq]
      exact hBx
    exact ball_subset_ball (by linarith [(hdata p).1]) hs
  have hterm (p : frontier U) : ContDiff ℝ 4 (fun x => B p x*w p x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (p : E) (r p)
    · exact (B p).contDiffAt.mul ((hdata p).2.1.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hd : r p/2 < dist x (p : E) := by
        have hh : r p ≤ dist x (p : E) := not_lt.mp hx
        linarith [(hdata p).1]
      have hn : ∀ᶠ y in 𝓝 x, r p/2 < dist y (p : E) :=
        (continuous_id.dist continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds hd)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      have hz : B p y = 0 := (B p).zero_of_le_dist hy.le
      simp only [hz,zero_mul]
  have hF : ContDiff ℝ 4 F := ContDiff.sum (fun p _ => hterm p)
  have hnegTerm (x : E) (hx : x ∈ U) (p : frontier U) : B p x*w p x ≤ 0 := by
    by_cases hz : B p x = 0
    · simp only [hz,zero_mul,le_refl]
    · exact mul_nonpos_of_nonneg_of_nonpos (B p).nonneg (((hdata p).2.2.1 x (hball p hz)).mp hx).le
  have hposTerm (x : E) (hx : x ∉ U) (p : frontier U) : 0 ≤ B p x*w p x := by
    by_cases hz : B p x = 0
    · simp only [hz,zero_mul,le_refl]
    · have hw : 0 ≤ w p x := not_lt.mp (fun hh => hx (((hdata p).2.2.1 x (hball p hz)).mpr hh))
      exact mul_nonneg (B p).nonneg hw
  have hFzero (x : E) (hx : x ∈ frontier U) : F x = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hz : B p x = 0
    · simp only [hz,zero_mul]
    · rw [(hdata p).2.2.2.1 x ⟨hball p hz,hx⟩,mul_zero]
  have hFnonpos (x : E) (hx : x ∈ U) : F x ≤ 0 :=
    Finset.sum_nonpos (fun p _ => hnegTerm x hx p)
  have hFnonneg (x : E) (hx : x ∉ U) : 0 ≤ F x :=
    Finset.sum_nonneg (fun p _ => hposTerm x hx p)
  refine ⟨F,hF,hFzero,hFnonpos,hFnonneg,W,isOpen_biUnion (fun _ _ => isOpen_ball),hcover,?_⟩
  intro x hxW
  constructor
  · intro hxU
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hxW
    have hBx : B p x = 1 := (B p).one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hxp).le)
    have hwx : w p x < 0 := ((hdata p).2.2.1 x
      (ball_subset_ball (by linarith [(hdata p).1]) hxp)).mp hxU
    have hh : ∑ p ∈ S, B p x*w p x < ∑ _p ∈ S, (0 : ℝ) :=
      Finset.sum_lt_sum (fun q _ => hnegTerm x hxU q) ⟨p,hp,by rw [hBx,one_mul]; exact hwx⟩
    simpa only [Finset.sum_const_zero] using hh
  · intro hneg
    by_contra hxU
    exact (not_lt_of_ge (hFnonneg x hxU)) hneg

end PowerConvexity
