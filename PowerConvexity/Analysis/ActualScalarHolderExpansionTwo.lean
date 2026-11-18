import PowerConvexity.Analysis.ActualScalarModulusExpansionTwo
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # Actual quadratic expansion with quantitative Holder input

The coefficient has qualitative C1 regularity and zero column divergence.
All approximation constants depend on its displayed Holder modulus and
ellipticity, without any bound for its first derivative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_weak_harmonic_holder_expansion_two
    {L alpha : ℝ} (hL : 0 ≤ L) (halpha : 0 < alpha) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖^alpha)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x| ≤ epsilon*‖x‖^alpha) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) ∧
        |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
        (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
        ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
          (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨R,hR,hRp⟩ := actual_positive_power_radius_two halpha
  obtain ⟨M,hM,r,hr,hrb,hrR,epsilon,heps,heps1,hcore⟩ :=
    actual_scalar_weak_harmonic_modulus_expansion_two hL hR
  have hrp : r^alpha ≤ (1/2 : ℝ) := hRp r hr.le hrR
  have hr1 : r ≤ 1 := by linarith
  refine ⟨M,hM,r,hr,hrb,hrp,epsilon,heps,heps1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  have hsub (n : ℕ) : ball (0 : E) (r^n) ⊆ ball (0 : E) 1 :=
    ball_subset_ball (pow_le_one₀ hr.le hr1)
  have hnorm (n : ℕ) (x : E) (hx : x ∈ ball (0 : E) (r^n)) :
      ‖x‖^alpha ≤ (1/2 : ℝ)^n :=
    actual_geometric_rpow_half_bound_two hr.le halpha.le hrp n (norm_nonneg x)
      (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hx))
  apply hcore A hlam hAL V hV hclosed hA hdiv ?_ f u hf ?_ hu uw hun
  · intro n x hx v
    exact (hdev x (hsub n hx) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnorm n x hx) heps.le) (norm_nonneg v))
  · intro n x hx
    exact (hfn x (hsub n hx)).trans (mul_le_mul_of_nonneg_left (hnorm n x hx) heps.le)

end PowerConvexity
