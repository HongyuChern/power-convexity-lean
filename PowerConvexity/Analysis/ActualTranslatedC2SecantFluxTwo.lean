import PowerConvexity.Analysis.ActualC2DifferenceQuotientJetsTwo

/-! # The genuine translated C2 secant flux

The field is expressed directly through the two actual cofactor matrices and
the actual first-jet difference quotient.  Its weak divergence is the true
density difference quotient; its limit is the linearized directional flux.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

def actualTranslatedC2SecantFluxTwo (u : E → ℝ) (v : E) (h : ℝ) (x : E) : E :=
  actualMatrixOperatorTwo ((1/2 : ℝ) • (complexCofactorCoeff u x+
    complexCofactorCoeff u (x+h • v)))
    (actualCovectorVectorTwo (actualLineDifferenceQuotientTwo (fderiv ℝ u) v h x))

theorem actual_translated_C2_secant_hasWeakDiv_two
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {u rho : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hrho : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det.re=rho x)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V)
    (v : E) (h : ℝ) (hshift : ∀ x ∈ V, x+h • v ∈ U) :
    HasWeakDiv (actualLineDifferenceQuotientTwo rho v h)
      (actualTranslatedC2SecantFluxTwo u v h) (ball c r) := by
  have htrans : ContDiffOn ℝ 2 (fun y => u (y+h • v)) V :=
    hu.comp (contDiffOn_id.add contDiffOn_const) hshift
  have hraw := actual_C2_midpoint_difference_quotient_hasWeakDiv_two hV
    (hu.mono hVU) htrans hclosed h
  apply actual_hasWeakDiv_congr_on_two isOpen_ball hraw
  · intro x hx
    have hxV := hclosed (ball_subset_closedBall hx)
    have hxU := hVU hxV
    have hxd := hshift x hxV
    have hx2 := hu.contDiffAt (hU.mem_nhds hxU)
    have hxd2 := hu.contDiffAt (hU.mem_nhds hxd)
    change h⁻¹ • actualMatrixOperatorTwo
      (complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+u (y+h • v))) x)
      (smoothGradField (fun y => u (y+h • v)-u y) x)=_
    rw [← map_smul,actual_difference_gradient_quotient_two
      (hx2.differentiableAt (by norm_num)) (hxd2.differentiableAt (by norm_num)),
      actual_midpoint_translated_cofactor_two hx2 hxd2]
    rfl
  · intro x hx
    have hxV := hclosed (ball_subset_closedBall hx)
    change h⁻¹*((complexHessian realDirections imagDirections (fun y => u (y+h • v)) x).det.re-
      (complexHessian realDirections imagDirections u x).det.re)=_
    rw [actual_complex_hessian_translate_two
      (hu.contDiffAt (hU.mem_nhds (hshift x hxV))),hrho x (hVU hxV),hrho _ (hshift x hxV)]
    rfl

theorem actual_covector_hessian_directional_gradient_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v : E) :
    actualCovectorVectorTwo (realHessian u x v)=smoothGradField (fun y => fderiv ℝ u y v) x := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  ext i
  change realHessian u x v (EuclideanSpace.single i 1)=
    fderiv ℝ (fun y => fderiv ℝ u y v) x (EuclideanSpace.single i 1)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_apply,
    _root_.add_apply,zero_add,ContinuousLinearMap.flip_apply]
  exact realHessian_symm hu v (EuclideanSpace.single i 1)

theorem actual_translated_C2_secant_flux_tendsto_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    {x : E} (hx : x ∈ U) (v : E) :
    Tendsto (fun h => actualTranslatedC2SecantFluxTwo u v h x) (𝓝[≠] 0)
      (𝓝 (matMulE (complexCofactorCoeff u x) (smoothGradField (fun y => fderiv ℝ u y v) x))) := by
  have hx2 := hu.contDiffAt (hU.mem_nhds hx)
  have hc : ContinuousAt (complexCofactorCoeff u) x :=
    (actual_C2_cofactor_continuousOn_two hU hu).continuousAt (hU.mem_nhds hx)
  have ht : Tendsto (fun h : ℝ => x+h • v) (𝓝[≠] 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) (𝓝[≠] 0) (𝓝 x)).add
        ((show Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 (0 : ℝ)) from nhdsWithin_le_nhds).smul
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => v) (𝓝[≠] 0) (𝓝 v)))
  have hM : Tendsto (fun h : ℝ => (1/2 : ℝ) •
      (complexCofactorCoeff u x+complexCofactorCoeff u (x+h • v))) (𝓝[≠] 0)
      (𝓝 (complexCofactorCoeff u x)) := by
    have hm : Tendsto (fun h : ℝ => (1/2 : ℝ) •
        (complexCofactorCoeff u x+complexCofactorCoeff u (x+h • v))) (𝓝[≠] 0)
        (𝓝 ((1/2 : ℝ) • (complexCofactorCoeff u x+complexCofactorCoeff u x))) :=
      (tendsto_const_nhds.add (hc.tendsto.comp ht)).const_smul (1/2 : ℝ)
    have he : (1/2 : ℝ) • (complexCofactorCoeff u x+complexCofactorCoeff u x)=
        complexCofactorCoeff u x := by
      ext i j
      simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
      ring
    rwa [he] at hm
  have hQ := actual_line_difference_quotient_tendsto_two
    ((hx2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) v
  have hOp := (actualMatrixOperatorTwo.continuous.tendsto _).comp hM
  have hVec := (actualCovectorVectorTwo.continuous.tendsto _).comp hQ
  have happ : Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hF := happ.continuousAt.tendsto.comp (hOp.prodMk_nhds hVec)
  simpa only [actualTranslatedC2SecantFluxTwo,Function.comp_def,← actual_covector_hessian_directional_gradient_two hx2 v,
    actual_matrix_operator_apply_two,realHessian] using hF

theorem actual_midpoint_matrix_operator_norm_le_two
    (A B : Mat) {M : ℝ} (hA : ‖actualMatrixOperatorTwo A‖ ≤ M)
    (hB : ‖actualMatrixOperatorTwo B‖ ≤ M) :
    ‖actualMatrixOperatorTwo ((1/2 : ℝ) • (A+B))‖ ≤ M := by
  rw [map_smul,map_add,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  have hh := mul_le_mul_of_nonneg_left
    (norm_add_le (actualMatrixOperatorTwo A) (actualMatrixOperatorTwo B))
    (by norm_num : (0 : ℝ) ≤ 1/2)
  linarith

theorem actual_translated_C2_secant_flux_norm_le_two
    {S : Set E} (hS : Convex ℝ S) {u : E → ℝ}
    (hu : ∀ x ∈ S, ContDiffAt ℝ 2 u x) {M H : ℝ} (hM : 0 ≤ M)
    (hA : ∀ x ∈ S, ‖actualMatrixOperatorTwo (complexCofactorCoeff u x)‖ ≤ M)
    (hH : ∀ x ∈ S, ‖realHessian u x‖ ≤ H)
    {x v : E} {h : ℝ} (hh : h ≠ 0) (hx : x ∈ S) (hxd : x+h • v ∈ S) :
    ‖actualTranslatedC2SecantFluxTwo u v h x‖ ≤ M*(‖actualCovectorVectorTwo‖*(H*‖v‖)) := by
  have hQ := actual_line_difference_quotient_norm_le_two hS
    (fun y hy => (((hu y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
    hH hh hx hxd
  have hG := (actualCovectorVectorTwo.le_opNorm
    (actualLineDifferenceQuotientTwo (fderiv ℝ u) v h x)).trans
    (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
  exact ((actualMatrixOperatorTwo ((1/2 : ℝ) • (complexCofactorCoeff u x+
    complexCofactorCoeff u (x+h • v)))).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (actual_midpoint_matrix_operator_norm_le_two _ _
      (hA x hx) (hA _ hxd)) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hG hM))

end PowerConvexity
