import PowerConvexity.Calculus.BallDirichletQuantitativeC0Two

/-! # Explicit O(t) convergence to the actual ball endpoint.
The estimate holds on the entire ambient space for the actual zero
extensions. It is not a derivative or spectral-minimum estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 160000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem minkowski_actual_solution_uniform_C0_rate_at_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A)
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A)
    (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u : Icc (0 : ℝ) 1 → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo a b A (ball 0 R) u) :
    let k := 2*L/rho
    ∀ t : Icc (0 : ℝ) 1, ∀ x : E,
      |(minkowskiDomain t A (ball 0 R)).indicator (u t) x-
        (minkowskiDomain (0 : ℝ) A (ball 0 R)).indicator (u ⟨0,by norm_num⟩) x| ≤
          ((2*k+k^2)*R^2)*(t : ℝ) := by
  let k : ℝ := 2*L/rho
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have hz := hu.endpoint_zero hab hAn hR
  have hzeq (x : E) :
      (minkowskiDomain (0 : ℝ) A (ball 0 R)).indicator (u ⟨0,by norm_num⟩) x =
        (ball (0 : E) R).indicator (quadraticBallPotential 1 R) x := by
    rw [minkowskiDomain_zero hAn]
    by_cases hx : x ∈ ball (0 : E) R
    · simp only [indicator_of_mem hx,hz (subset_closure hx)]
    · simp only [indicator_of_notMem hx]
  dsimp only
  intro t x
  let lam : ℝ := 1+k*(t : ℝ)
  have hlam : 1 ≤ lam := by
    dsimp only [lam]
    exact le_add_of_nonneg_right (mul_nonneg hk t.2.1)
  have htr := minkowskiDomain_homothetic_trapping hconv (convex_ball (0 : E) R)
    hrho hL hballA hballB hAb hBb (0 : ℝ) (t : ℝ)
  dsimp only at htr
  have he : 1+2*L*|(t : ℝ)-0|/rho = lam := by
    rw [sub_zero,abs_of_nonneg t.2.1]
    dsimp only [lam,k]
    ring
  rw [he,minkowskiDomain_zero hAn] at htr
  have hbd := classicalDirichlet_ball_trapping_uniform_C0_two
    (minkowskiDomain_isOpen hA isOpen_ball hAn (t : ℝ))
    (minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2)
    a b hab hR hlam htr.1 htr.2 (hu t) x
  rw [hzeq x]
  apply hbd.trans
  have hlin : lam^2-1 ≤ (2*k+k^2)*(t : ℝ) := by
    have ht : 0 ≤ (t : ℝ)-(t : ℝ)^2 := by nlinarith only [t.2.1,t.2.2]
    have hp := mul_nonneg (sq_nonneg k) ht
    dsimp only [lam]
    nlinarith only [hp]
  have hh := mul_le_mul_of_nonneg_right hlin (sq_nonneg R)
  simpa only [k,mul_assoc,mul_left_comm,mul_comm] using hh

end PowerConvexity
