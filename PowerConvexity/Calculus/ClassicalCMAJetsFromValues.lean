import PowerConvexity.Calculus.ClassicalCMASecondJetContinuity
import PowerConvexity.Calculus.BoundedHessianFirstJetContinuity

/-! # Noncircular joint first and second jets of classical CMA families

Joint C0 values and the uniform real Hessian bound on the larger ball give
the first jets by the mean value theorem. The same Hessian bound then
feeds the pinned CHS estimate, giving the second jets. Power convexity is
not an input or a dependency of these proofs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {n : ℕ} {T : Type*} [TopologicalSpace T]
local notation "E" => DeGiorgi.AmbientSpace (n+n)

theorem realHessian_family_continuousAt_of_values_CMA_entry_bound
    (hn : 2 ≤ n) {u : T → E → ℝ} {t0 : T} {x0 : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hval : ∀ y ∈ closedBall x0 (3*R),
      ContinuousAt (fun p : T × E => u p.1 p.2) (t0,y))
    (hdata : ∀ᶠ t in 𝓝 t0,
      ContDiffOn ℝ 4 (u t) (ball x0 (4*R)) ∧
      (∀ x ∈ ball x0 (4*R), (complexHessian realDirections imagDirections (u t) x).det = 1) ∧
      (∀ x ∈ ball x0 (4*R), (complexHessian realDirections imagDirections (u t) x).PosDef) ∧
      (∀ x ∈ ball x0 (4*R), ∀ i j, |euclideanHessian (u t) x i j| ≤ M)) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,x0) ∧
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  have hD (y : E) (hy : y ∈ closedBall x0 R) :
      ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,y) := by
    have hsub (z : E) (hz : z ∈ closedBall y R) : z ∈ closedBall x0 (3*R) := by
      rw [mem_closedBall] at hy hz ⊢
      have hh := dist_triangle z y x0
      linarith
    have hlarge (z : E) (hz : z ∈ closedBall y R) : z ∈ ball x0 (4*R) :=
      (closedBall_subset_ball (by linarith : 3*R < 4*R)) (hsub z hz)
    apply fderiv_family_continuousAt_of_joint_values_boundedHessian
      hR (by positivity : 0 ≤ ((n+n : ℕ) : ℝ)^2*M)
      (fun z hz => hval z (hsub z hz))
    filter_upwards [hdata] with t ht
    intro z hz
    refine ⟨(ht.1.contDiffAt (isOpen_ball.mem_nhds (hlarge z hz))).of_le (by norm_num),?_⟩
    have hh := euclidean_bilinear_norm_le_of_entry_bound
      (realHessian (u t) z) hM (ht.2.2.2 z (hlarge z hz))
    simpa only [Fintype.card_fin] using hh
  exact ⟨hD x0 (mem_closedBall_self hR.le),
    realHessian_family_continuousAt_of_CMA_entry_bound hn hR hM hD hdata⟩

theorem realHessian_family_continuousAt_of_values_CMA_boundary_upper
    (hn : 2 ≤ n) {u : T → E → ℝ} {U : T → Set E}
    (J : ∀ t, ClosureC2Jet (u t) (U t)) {t0 : T} {x0 : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hval : ∀ y ∈ closedBall x0 (3*R),
      ContinuousAt (fun p : T × E => u p.1 p.2) (t0,y))
    (hdata : ∀ᶠ t in 𝓝 t0,
      IsOpen (U t) ∧ IsCompact (closure (U t)) ∧
      ContDiffOn ℝ 4 (u t) (U t) ∧
      (∀ x ∈ frontier (U t), u t x = 0) ∧
      (∀ x ∈ U t, (complexHessian realDirections imagDirections (u t) x).PosDef) ∧
      (∀ x ∈ U t, (complexHessian realDirections imagDirections (u t) x).det = 1) ∧
      ball x0 (4*R) ⊆ U t ∧
      (∀ x ∈ frontier (U t), ∀ v : E, (J t).hessian x v v ≤ M*‖v‖^2)) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,x0) ∧
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  apply realHessian_family_continuousAt_of_values_CMA_entry_bound hn hR
    (by positivity : 0 ≤ 3*M) hval
  filter_upwards [hdata] with t ht
  rcases ht with ⟨hU,hK,hu,hb,hpos,hdet,hball,hboundary⟩
  refine ⟨hu.mono hball,fun x hx => hdet x (hball hx),
    fun x hx => hpos x (hball hx),?_⟩
  intro x hx i j
  exact euclideanHessian_abs_le_of_boundary_quadratic_upper
    hU hK hu (J t) hb hpos hdet hM hboundary x (hball hx) i j

end PowerConvexity
