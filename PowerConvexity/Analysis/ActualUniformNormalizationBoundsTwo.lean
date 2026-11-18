import PowerConvexity.Analysis.ActualPhysicalQuadraticTwo

/-! # Uniform bounds for the actual frozen normalizing maps

The coefficient's almost-everywhere ellipticity is promoted pointwise using
entry continuity on the actual open set. Every frozen normalization then has
operator bounds determined by the same original ellipticity constants. No
continuous choice of eigenvectors or of normalizing maps is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuousOn_le_of_ae_two {U : Set E} (hU : IsOpen U)
    {f g : E → ℝ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : ∀ᵐ x ∂volume.restrict U, f x ≤ g x) : ∀ x ∈ U, f x ≤ g x := by
  have he : (fun x => max (f x) (g x)) =ᵐ[volume.restrict U] g := by
    filter_upwards [hfg] with x hx
    exact max_eq_right hx
  have hp := Measure.eqOn_open_of_ae_eq he hU (hf.sup hg) hg
  intro x hx
  exact (le_max_left _ _).trans (hp hx).le

theorem actual_continuous_matrix_action_two {U : Set E} {a : E → Mat}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) U) (v : E) :
    ContinuousOn (fun x => matMulE (a x) v) U := by
  have hm : ContinuousOn a U := continuousOn_pi.mpr (fun i =>
    continuousOn_pi.mpr (fun j => ha i j))
  exact (actualMatrixOperatorTwo.continuous.comp_continuousOn hm).clm_apply continuousOn_const

theorem actual_elliptic_bounds_pointwise_two {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U) :
    ∀ x ∈ U, ∀ v : E,
      A.lam*‖v‖^2 ≤ ⟪v,matMulE (A.a x) v⟫_ℝ ∧
        ⟪v,matMulE (A.a x) v⟫_ℝ ≤ A.Λ*‖v‖^2 := by
  intro x hx v
  have hc : ContinuousOn (fun y => ⟪v,matMulE (A.a y) v⟫_ℝ) U :=
    continuousOn_const.inner (actual_continuous_matrix_action_two ha v)
  exact ⟨actual_continuousOn_le_of_ae_two hU continuousOn_const hc
    (A.coercive.mono (fun y hy => hy v)) x hx,
    actual_continuousOn_le_of_ae_two hU hc continuousOn_const
      (A.quadratic_upper.mono (fun y hy => hy v)) x hx⟩

theorem actual_frozen_normalization_adjoint_energy_two
    (G : E ≃L[ℝ] E) {A : Mat} (hA : actualLinearCongruenceMatrixTwo G A = 1)
    (v : E) :
    ‖G.toContinuousLinearMap.adjoint v‖^2 = ⟪v,matMulE A v⟫_ℝ := by
  rw [actual_normalization_recovers_factor_two G hA,actual_matMulE_mul_two,
    actual_linear_matrix_transpose_action_two,actual_linear_matrix_action_two]
  exact (real_inner_self_eq_norm_sq _).symm.trans
    (ContinuousLinearMap.adjoint_inner_left G.toContinuousLinearMap
      (G.toContinuousLinearMap.adjoint v) v)

theorem actual_frozen_normalization_operator_bounds_two
    (G : E ≃L[ℝ] E) {A : Mat} (hA : actualLinearCongruenceMatrixTwo G A = 1)
    {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlo : ∀ v : E, lam*‖v‖^2 ≤ ⟪v,matMulE A v⟫_ℝ)
    (hhi : ∀ v : E, ⟪v,matMulE A v⟫_ℝ ≤ Lambda*‖v‖^2) :
    ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ := by
  have hG : ‖G.toContinuousLinearMap.adjoint‖ ≤ Real.sqrt Lambda := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hb := hhi v
    rw [← actual_frozen_normalization_adjoint_energy_two G hA] at hb
    have hs := Real.sq_sqrt hLambda.le
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
    simpa only [mul_pow,hs] using hb
  have hInv : ‖G.symm.toContinuousLinearMap.adjoint‖ ≤ (Real.sqrt lam)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    intro v
    let w := G.symm.toContinuousLinearMap.adjoint v
    have hrecover : G.toContinuousLinearMap.adjoint w = v := by
      simpa only [G.symm_symm] using actual_linear_adjoint_inverse_apply_two G.symm v
    have hb := hlo w
    rw [← actual_frozen_normalization_adjoint_energy_two G hA,hrecover] at hb
    have hsq := Real.sq_sqrt hlam.le
    have hsqrt := Real.sqrt_pos.mpr hlam
    have hprod : Real.sqrt lam*‖w‖ ≤ ‖v‖ := by
      apply (sq_le_sq₀ (mul_nonneg hsqrt.le (norm_nonneg w)) (norm_nonneg v)).mp
      simpa only [mul_pow,hsq] using hb
    change ‖w‖ ≤ (Real.sqrt lam)⁻¹*‖v‖
    rw [inv_mul_eq_div,le_div_iff₀ hsqrt]
    simpa only [mul_comm] using hprod
  simpa only [ContinuousLinearMap.adjoint.norm_map] using And.intro hG hInv

theorem actual_all_frozen_normalizations_uniform_two {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U) :
    ∀ x ∈ U, ∀ G : E ≃L[ℝ] E,
      actualLinearCongruenceMatrixTwo G (A.a x) = 1 →
      ‖G.toContinuousLinearMap‖ ≤ Real.sqrt A.Λ ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt A.lam)⁻¹ := by
  intro x hx G hfreeze
  have hb := actual_elliptic_bounds_pointwise_two hU A ha x hx
  exact actual_frozen_normalization_operator_bounds_two G hfreeze A.hlam A.Λ_pos
    (fun v => (hb v).1) (fun v => (hb v).2)

theorem actual_normalized_ellipticity_upper_uniform_two {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U)
    {x : E} (hx : x ∈ U) (G : E ≃L[ℝ] E)
    (hfreeze : actualLinearCongruenceMatrixTwo G (A.a x) = 1) :
    (actualLinearPullbackCoeffTwo G A).Λ ≤
      A.Λ*(max 1 (Real.sqrt A.lam)⁻¹)^2 := by
  have hb := (actual_all_frozen_normalizations_uniform_two hU A ha x hx G hfreeze).2
  change A.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2 ≤ _
  apply mul_le_mul_of_nonneg_left _ A.Λ_nonneg
  have hm := max_le_max_left (1 : ℝ) hb
  nlinarith [le_max_left (1 : ℝ) ‖G.symm.toContinuousLinearMap‖,
    le_max_left (1 : ℝ) (Real.sqrt A.lam)⁻¹]

end PowerConvexity
