import PowerConvexity.Analysis.ActualScalarQuadraticLimitErrorTwo
import PowerConvexity.Analysis.ActualScalarModulusSequenceTwo

/-! # Actual second-order L2 approximation of the original weak function.
The single harmonic quadratic is constructed from the proved sequence.
Its error has the full four-dimensional quadratic scaling at every scale.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_weak_harmonic_modulus_expansion_two {L Rmax : ℝ} (hL : 0 ≤ L) (hRmax : 0 < Rmax) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ Rmax ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ n : ℕ, ∀ x ∈ ball (0 : E) (r^n), ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*(1/2 : ℝ)^n)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ n : ℕ, ∀ x ∈ ball (0 : E) (r^n), |f x| ≤ epsilon*(1/2 : ℝ)^n) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) ∧
        |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
        (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
        ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
          (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨M,hM,r,hr,hrb,hrmax,epsilon,heps,heps1,hseq⟩ := actual_scalar_quadratic_modulus_sequence_two hL hRmax
  refine ⟨M,hM,r,hr,hrb,hrmax,epsilon,heps,heps1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  obtain ⟨Q,hQ0,hs,hi⟩ := hseq A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  exact actual_scalar_quadratic_limit_error_two hM.le hr (by linarith) uw.memLp hQ0 hs hi

end PowerConvexity
