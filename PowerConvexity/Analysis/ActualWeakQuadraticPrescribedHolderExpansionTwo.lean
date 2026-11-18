import PowerConvexity.Analysis.ActualWeakQuadraticPrescribedHolderSequenceTwo
import PowerConvexity.Analysis.ActualWeakQuadraticHolderNormalizationTwo
import PowerConvexity.Analysis.ActualScalarPrescribedHolderExpansionTwo

/-! # Actual prescribed-alpha weak expansion for continuous coefficients

No coefficient derivative occurs. Full weak quadratic source identities
supply the polynomial subtraction, and all scales and errors retain the
input alpha and the same actual weak solution.
-/
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

theorem actual_weak_quadratic_prescribed_holder_expansion_two
    {L alpha : ℝ} (hL : 0 ≤ L) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall (0 : E) 1)) →
      ActualWeakQuadraticSourcesTwo A →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖^alpha)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x| ≤ epsilon*‖x‖^alpha) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace=0) ∧
        |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
        (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
        ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
          (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((r^alpha)^n)^2*(r^n)^8 := by
  obtain ⟨M,hM,r,hr,hrb,_,hralpha,epsilon,heps,heps1,hseq⟩ :=
    actual_weak_quadratic_prescribed_holder_modulus_sequence_two hL (by norm_num : (0 : ℝ) < 1)
      halpha halpha1
  have hr1 : r ≤ 1 := by linarith
  have htheta : 0 < r^alpha := Real.rpow_pos_of_pos hr alpha
  refine ⟨M,hM,r,hr,hrb,hralpha,epsilon,heps,heps1,?_⟩
  intro A hlam hAL hA hquad hdev f u hf hfn hu uw hun
  have hsub (n : ℕ) : ball (0 : E) (r^n) ⊆ ball (0 : E) 1 :=
    ball_subset_ball (pow_le_one₀ hr.le hr1)
  have hnorm (n : ℕ) (x : E) (hx : x ∈ ball (0 : E) (r^n)) :
      ‖x‖^alpha ≤ (r^alpha)^n := by
    calc
      ‖x‖^alpha ≤ (r^n)^alpha := Real.rpow_le_rpow (norm_nonneg x)
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hx)) halpha.le
      _ = (r^alpha)^n := actual_nat_power_rpow_comm_two hr.le alpha n
  obtain ⟨Q,hQ0,hs,hi⟩ := hseq A hlam hAL hA hquad
    (fun n x hx v => (hdev x (hsub n hx) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnorm n x hx) heps.le) (norm_nonneg v)))
    f u hf (fun n x hx => (hfn x (hsub n hx)).trans
      (mul_le_mul_of_nonneg_left (hnorm n x hx) heps.le)) hu uw hun
  exact actual_scalar_geometric_limit_error_two hM.le hr hr1 htheta hralpha uw.memLp hQ0 hs hi


theorem actual_weak_quadratic_prescribed_holder_general_source_expansion_two {L alpha : ℝ}
    (hL : 0 ≤ L) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall (0 : E) 1)) →
      ActualWeakQuadraticSourcesTwo A →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖^alpha)*‖v‖) →
      ∀ (f u : E → ℝ) (b K N : ℝ), 0 ≤ K →
      MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x-b| ≤ K*‖x‖^alpha) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ N →
      ∃ S > 0, S ≤ N+(|b|/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal+
          (K+|b| * epsilon)/epsilon+1 ∧
        ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
          (∀ x, (realBlockHessian realDirections imagDirections p x).trace = -b) ∧
          |p 0| ≤ S*(2*M) ∧ ‖fderiv ℝ p 0‖ ≤ S*(2*M) ∧
          (∀ x, ‖realHessian p x‖ ≤ |b|/4+S*(2*M)) ∧
          ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
            S^2*(2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((r^alpha)^n)^2*(r^n)^8 := by
  obtain ⟨M,hM,r,hr,hrb,hralpha,epsilon,heps,heps1,hcore⟩ := actual_weak_quadratic_prescribed_holder_expansion_two hL halpha halpha1
  refine ⟨M,hM,r,hr,hrb,hralpha,epsilon,heps,heps1,?_⟩
  intro A hlam hAL hA hquad hdev f u b K N hK hf hfn hu uw hun
  obtain ⟨S,hS,hSN,hgf,hgn,hvw,ww,hwn⟩ := actual_weak_quadratic_holder_corrected_normalization_two heps hK
    A hA hquad hdev hf hfn hu uw hun
  let v : E → ℝ := fun x => S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)
  let g : E → ℝ := fun x => S⁻¹*(f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x)
  obtain ⟨p,hp,hpt,hp0,hp1,hp2,herr⟩ := hcore A hlam hAL hA hquad hdev
    g v hgf hgn hvw ww hwn
  obtain ⟨hp',hpt',hp0',hp1',hp2'⟩ := actual_scalar_corrected_quadratic_properties_two
    (b := b) hp hS.le hpt hp0 hp1 hp2
  refine ⟨S,hS,hSN,scalarCorrectedQuadraticTwo b S p,hp',hpt',hp0',hp1',hp2',?_⟩
  intro n
  rw [actual_scalar_unnormalized_error_identity_two hS]
  exact (mul_le_mul_of_nonneg_left (herr n) (sq_nonneg S)).trans_eq (by ring)


end PowerConvexity
