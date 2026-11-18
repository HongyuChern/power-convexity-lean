import PowerConvexity.Analysis.ActualScalarPolynomialUnnormalizationTwo

/-! # Actual scalar quadratic expansion with arbitrary source value.
All constants preceding A,f,u are uniform. The amplitude is constructed
and bounded by the original L2 norm, source value and source growth.
The single actual quadratic has the correct frozen equation at the center.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_general_source_quadratic_expansion_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) →
      ∀ (f u : E → ℝ) (b K N : ℝ), 0 ≤ K →
      MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x-b| ≤ K*‖x‖) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ N →
      ∃ S > 0, S ≤ N+(|b|/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal+
          (K+|b| * epsilon)/epsilon+1 ∧
        ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
          (∀ x, (realBlockHessian realDirections imagDirections p x).trace = -b) ∧
          |p 0| ≤ S*(2*M) ∧ ‖fderiv ℝ p 0‖ ≤ S*(2*M) ∧
          (∀ x, ‖realHessian p x‖ ≤ |b|/4+S*(2*M)) ∧
          ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
            S^2*(2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,hcore⟩ := actual_scalar_weak_harmonic_quadratic_expansion_two hL
  refine ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u b K N hK hf hfn hu uw hun
  obtain ⟨S,hS,hSN,hgf,hgn,hvw,ww,hwn⟩ := actual_scalar_corrected_normalization_two heps hK
    A hV hclosed hA hdiv hdev hf hfn hu uw hun
  let v : E → ℝ := fun x => S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)
  let g : E → ℝ := fun x => S⁻¹*(f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x)
  obtain ⟨p,hp,hpt,hp0,hp1,hp2,herr⟩ := hcore A hlam hAL V hV hclosed hA hdiv hdev
    g v hgf hgn hvw ww hwn
  obtain ⟨hp',hpt',hp0',hp1',hp2'⟩ := actual_scalar_corrected_quadratic_properties_two
    (b := b) hp hS.le hpt hp0 hp1 hp2
  refine ⟨S,hS,hSN,scalarCorrectedQuadraticTwo b S p,hp',hpt',hp0',hp1',hp2',?_⟩
  intro n
  rw [actual_scalar_unnormalized_error_identity_two hS]
  exact (mul_le_mul_of_nonneg_left (herr n) (sq_nonneg S)).trans_eq (by ring)

end PowerConvexity
