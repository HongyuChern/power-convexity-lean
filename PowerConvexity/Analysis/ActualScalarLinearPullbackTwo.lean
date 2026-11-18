import PowerConvexity.Analysis.ActualLinearGradientCalculusTwo

/-! # Actual full scalar weak equation under linear coordinates.
The target coefficient is required to be the actual inverse congruence.
The conclusion quantifies over all actual H01 tests and all their witnesses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_linear_adjoint_inverse_apply_two (G : E ≃L[ℝ] E) (v : E) :
    G.symm.toContinuousLinearMap.adjoint (G.toContinuousLinearMap.adjoint v) = v := by
  have he : G.toContinuousLinearMap.comp G.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by
    ext x
    simp
  have hh := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at hh
  exact congrArg (fun F : E →L[ℝ] E => F v) hh

theorem actual_linear_congruence_pairing_two (G : E ≃L[ℝ] E)
    (A B : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    (hB : ∀ v : E, matMulE B v =
      G.symm (matMulE A (G.symm.toContinuousLinearMap.adjoint v))) (v w : E) :
    ⟪matMulE B (G.toContinuousLinearMap.adjoint v),G.toContinuousLinearMap.adjoint w⟫_ℝ =
      ⟪matMulE A v,w⟫_ℝ := by
  rw [hB,actual_linear_adjoint_inverse_apply_two,ContinuousLinearMap.adjoint_inner_right]
  simp

theorem actual_scalar_weak_linear_pullback_two {U : Set E}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (G : E ≃L[ℝ] E)
    (A : EllipticCoeff (2+2) U) (B : EllipticCoeff (2+2) (G ⁻¹' U))
    (hB : ∀ z ∈ G ⁻¹' U, ∀ v : E, matMulE (B.a z) v =
      G.symm (matMulE (A.a (G z)) (G.symm.toContinuousLinearMap.adjoint v)))
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo B (fun z => f (G z)) (fun z => u (G z)) := by
  let uw := hu.1.someWitness
  let vw := actual_linear_pullback_witness_two G uw
  have hV : IsOpen (G ⁻¹' U) := hU.preimage G.continuous
  have hVb : Bornology.IsBounded (G ⁻¹' U) := G.antilipschitz.isBounded_preimage hUb
  have hfg := actual_memLp_linear_pullback_two G hf
  obtain ⟨C,hC,hP⟩ := zeroTrace_poincare_L2_witness_bound (by norm_num : 2 ≤ 2+2) hV hVb
  refine ⟨vw.memW1p,?_⟩
  refine bilinFormOfCoeff_eq_of_isSmoothTestOn hV B
    (fun phi => ∫ z in G ⁻¹' U, f (G z)*phi z) ?_ ?_ (‖hfg.toLp (fun z => f (G z))‖*C) ?_ vw ?_
  · intro a b ha hb
    simp only [mul_add]
    exact integral_add (hfg.integrable_mul ha.1.1) (hfg.integrable_mul hb.1.1)
  · intro c a ha
    have he : (fun z => f (G z)*(c*a z)) = (fun z => c*(f (G z)*a z)) := by
      funext z; ring
    rw [he,integral_const_mul]
  · intro a ha aw
    have hh := (scalar_L2_integral_mul_bound hfg aw.memLp).trans
      (mul_le_mul_of_nonneg_left (hP a ha aw) (norm_nonneg (hfg.toLp (fun z => f (G z)))))
    simpa only [norm_gradLpOfWitness_eq,mul_assoc] using hh
  · intro phi hp
    let psi : E → ℝ := fun x => phi (G.symm x)
    have hp' : IsSmoothTestOn U psi := actual_smooth_test_linear_pushforward_two G hp
    have key := hu.2 uw psi (smoothTest_memH01 hU hp') (smoothTestWitness hU hp')
    have he : bilinFormOfCoeff B vw (smoothTestWitness hV hp) =
        |(LinearMap.det G.toLinearMap)⁻¹| * bilinFormOfCoeff A uw (smoothTestWitness hU hp') := by
      unfold bilinFormOfCoeff
      rw [← actual_setIntegral_linear_pullback_two G]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      change ⟪matMulE (B.a z) (actualLinearWeakGradientTwo G uw.weakGrad z),
          smoothGradField phi z⟫_ℝ =
        ⟪matMulE (A.a (G z)) (uw.weakGrad (G z)),smoothGradField psi (G z)⟫_ℝ
      rw [actual_linear_weak_gradient_adjoint_two,
        ← actual_smooth_gradient_inverse_pullback_two G (hp.1.differentiable (by simp)) z]
      exact actual_linear_congruence_pairing_two G (A.a (G z)) (B.a z) (hB z hz) _ _
    rw [he,key,← actual_setIntegral_linear_pullback_two G]
    simp only [psi,G.symm_apply_apply]

end PowerConvexity
