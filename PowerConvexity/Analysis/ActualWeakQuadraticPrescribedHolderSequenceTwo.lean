import PowerConvexity.Analysis.ActualWeakQuadraticPrescribedHolderRecursiveTwo
import PowerConvexity.Analysis.ActualScalarPrescribedHolderSequenceTwo

/-! # Same-solution geometric iteration with actual weak quadratic sources -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_weak_quadratic_prescribed_holder_modulus_sequence_two {L Rmax alpha : ℝ}
    (hL : 0 ≤ L) (hRmax : 0 < Rmax) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ Rmax ∧ r^alpha ≤ (1/2 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall (0 : E) 1)) →
      ActualWeakQuadraticSourcesTwo A →
      (∀ n : ℕ, ∀ x ∈ ball (0 : E) (r^n), ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*(r^alpha)^n)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ n : ℕ, ∀ x ∈ ball (0 : E) (r^n), |f x| ≤ epsilon*(r^alpha)^n) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ Q : ℕ → E → ℝ, Q 0 = (fun _ => 0) ∧
        (∀ n, ActualScalarGeometricStateTwo u M r (r^alpha) n (Q n)) ∧
        (∀ n, ActualScalarGeometricIncrementTwo M r (r^alpha) n (Q n) (Q (n+1))) := by
  obtain ⟨M,hM,r,hr,hrb,hrmax,hralpha,epsilon,heps,heps1,hstep⟩ :=
    actual_weak_quadratic_prescribed_holder_recursive_step_two hL hRmax halpha halpha1
  have htheta : 0 < r^alpha := Real.rpow_pos_of_pos hr alpha
  refine ⟨M,hM,r,hr,hrb,hrmax,hralpha,epsilon,heps,heps1,?_⟩
  intro A hlam hAL hA hquad hdev f u hf hfn hu uw hun
  let P := ActualScalarGeometricStateTwo u M r (r^alpha)
  let I := ActualScalarGeometricIncrementTwo M r (r^alpha)
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
    · have he : normalizedScalarResidualTwo u (fun _ => 0) (r^0) ((r^alpha)^0) = u := by
        funext z
        simp [normalizedScalarResidualTwo]
      exact htransport he ⟨uw,hun⟩
  have hnext : ∀ n q, P n q → ∃ q', P (n+1) q' ∧ I n q q' := by
    intro n q hqstate
    obtain ⟨hq,hqt,hqH,ww,hwn⟩ := hqstate
    have hRn : 0 < r^n := pow_pos hr n
    have han : 0 < (r^alpha)^n := pow_pos htheta n
    have hRn1 : r^n ≤ 1 := pow_le_one₀ hr.le (by linarith)
    have han1 : (r^alpha)^n ≤ 1 := pow_le_one₀ htheta.le (by linarith)
    obtain ⟨q',hq',hqt',hqH',h0,h1,h2,ww',hwn'⟩ :=
      hstep A hlam hAL hA hquad f u hf hu
        (r^n) ((r^alpha)^n) hRn han hRn1 han1 (hdev n) (hfn n) q hq hqt hqH ww hwn
    have he : (r^alpha)^n*r^alpha = (r^alpha)^(n+1) := (pow_succ _ _).symm
    refine ⟨q',?_,h0,h1,h2⟩
    refine ⟨hq',hqt',?_,?_⟩
    · intro x
      simpa only [he] using hqH' x
    · change ∃ w : MemW1pWitness 2
          (normalizedScalarResidualTwo u q' (r^(n+1)) ((r^alpha)^(n+1))) _, _
      have her : normalizedScalarResidualTwo u q' (r^(n+1)) ((r^alpha)^(n+1)) =
          normalizedScalarResidualTwo u q' (r^n*r) ((r^alpha)^n*r^alpha) := by
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
