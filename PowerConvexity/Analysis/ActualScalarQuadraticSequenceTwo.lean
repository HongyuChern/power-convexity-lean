import PowerConvexity.Analysis.ActualScalarRecursiveStepTwo

/-! # Construction of the actual quadratic sequence for a fixed weak solution.
The sequence is built by dependent recursion from the proved PDE step.
No approximating sequence, classical jet or convergence is assumed.
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

def ActualScalarQuadraticStateTwo (u : E → ℝ) (M r : ℝ) (n : ℕ) (q : E → ℝ) : Prop :=
  IsQuadraticPolynomial q ∧
  (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
  (∀ x, ‖realHessian q x‖ ≤ 2*M*(1-(1/2 : ℝ)^n)) ∧
  ∃ ww : MemW1pWitness 2 (normalizedScalarResidualTwo u q (r^n) ((1/2 : ℝ)^n))
    (ball (0 : E) 1),
    ‖ww.memLp.toLp (normalizedScalarResidualTwo u q (r^n) ((1/2 : ℝ)^n))‖ ≤ 1

def ActualScalarQuadraticIncrementTwo (M r : ℝ) (n : ℕ) (q q' : E → ℝ) : Prop :=
  |q' 0-q 0| ≤ (1/2 : ℝ)^n*(r^n)^2*M ∧
  ‖fderiv ℝ q' 0-fderiv ℝ q 0‖ ≤ (1/2 : ℝ)^n*r^n*M ∧
  ∀ x, ‖realHessian q' x-realHessian q x‖ ≤ (1/2 : ℝ)^n*M

theorem actual_scalar_quadratic_sequence_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x| ≤ epsilon*‖x‖) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ Q : ℕ → E → ℝ, Q 0 = (fun _ => 0) ∧
        (∀ n, ActualScalarQuadraticStateTwo u M r n (Q n)) ∧
        (∀ n, ActualScalarQuadraticIncrementTwo M r n (Q n) (Q (n+1))) := by
  obtain ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,hstep⟩ := actual_scalar_recursive_step_two hL
  refine ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  let P := ActualScalarQuadraticStateTwo u M r
  let I := ActualScalarQuadraticIncrementTwo M r
  have hHzero (x : E) : realHessian (fun _ : E => (0 : ℝ)) x = 0 := by
    unfold realHessian
    simp
  have hTzero (x : E) : (realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x).trace = 0 := by
    have he : realBlockHessian realDirections imagDirections (fun _ : E => (0 : ℝ)) x = 0 := by
      ext i j
      unfold realBlockHessian
      rw [hHzero]
      rfl
    rw [he,Matrix.trace_zero]
  have htransport {v w : E → ℝ} (he : v = w)
      (hw : ∃ ww : MemW1pWitness 2 w (ball (0 : E) 1), ‖ww.memLp.toLp w‖ ≤ 1) :
      ∃ vw : MemW1pWitness 2 v (ball (0 : E) 1), ‖vw.memLp.toLp v‖ ≤ 1 := by
    subst w
    exact hw
  have hzero : P 0 (fun _ => 0) := by
    refine ⟨(quadraticSubmodule E).zero_mem,?_,?_,?_⟩
    · exact hTzero
    · intro x
      rw [hHzero]
      have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 := norm_zero
      rw [hz]
      norm_num
    · have he : normalizedScalarResidualTwo u (fun _ => 0) (r^0) ((1/2 : ℝ)^0) = u := by
        funext z
        simp [normalizedScalarResidualTwo]
      exact htransport he ⟨uw,hun⟩
  have hnext : ∀ n q, P n q → ∃ q', P (n+1) q' ∧ I n q q' := by
    intro n q hqstate
    obtain ⟨hq,hqt,hqH,ww,hwn⟩ := hqstate
    have hRn : 0 < r^n := pow_pos hr n
    have han : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
    have hRan : r^n ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ hr.le (by linarith) n
    have han1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    obtain ⟨q',hq',hqt',hqH',h0,h1,h2,ww',hwn'⟩ :=
      hstep A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu
        (r^n) ((1/2 : ℝ)^n) hRn han hRan han1 q hq hqt hqH ww hwn
    have he : (1/2 : ℝ)^n/2 = (1/2 : ℝ)^(n+1) := by rw [pow_succ];ring
    refine ⟨q',?_,h0,h1,h2⟩
    refine ⟨hq',hqt',?_,?_⟩
    · intro x
      simpa only [he] using hqH' x
    · change ∃ w : MemW1pWitness 2
          (normalizedScalarResidualTwo u q' (r^(n+1)) ((1/2 : ℝ)^(n+1))) _, _
      have her : normalizedScalarResidualTwo u q' (r^(n+1)) ((1/2 : ℝ)^(n+1)) =
          normalizedScalarResidualTwo u q' (r^n*r) ((1/2 : ℝ)^n/2) := by
        rw [show r^(n+1) = r^n*r from pow_succ r n,← he]
      exact htransport her ⟨ww',hwn'⟩
  let next (n : ℕ) (q : {q : E → ℝ // P n q}) : {q : E → ℝ // P (n+1) q} :=
    ⟨Classical.choose (hnext n q.val q.property),
      (Classical.choose_spec (hnext n q.val q.property)).1⟩
  let S : (n : ℕ) → {q : E → ℝ // P n q} :=
    fun n => Nat.rec (motive := fun n => {q : E → ℝ // P n q})
      ⟨fun _ => 0,hzero⟩ (fun n q => next n q) n
  let Q : ℕ → E → ℝ := fun n => (S n).val
  refine ⟨Q,rfl,(fun n => (S n).property),?_⟩
  intro n
  change I n (S n).val (next n (S n)).val
  exact (Classical.choose_spec (hnext n (S n).val (S n).property)).2

end PowerConvexity
