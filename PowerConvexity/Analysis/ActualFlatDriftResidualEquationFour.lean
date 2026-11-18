import PowerConvexity.Analysis.ActualFlatResidualEquationFour

/-! # Exact residual scaling for the full non-divergence equation with drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatDriftResidualSourceFour (A : E → Mat) (b : E → E)
    (f q : E → ℝ) (R a : ℝ) (z : E) : ℝ :=
  a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)+fderiv ℝ q (R • z) (b (R • z)))

theorem actual_normalized_residual_fderiv_four {u q : E → ℝ} {R a : ℝ}
    (hR : 0 < R) {z : E} (hu : DifferentiableAt ℝ u (R • z))
    (hq : DifferentiableAt ℝ q (R • z)) :
    fderiv ℝ (normalizedScalarResidualTwo u q R a) z =
      (a⁻¹*R⁻¹) • (fderiv ℝ u (R • z)-fderiv ℝ q (R • z)) := by
  change fderiv ℝ ((a⁻¹*(R^2)⁻¹) • (fun y => (u-q) (R • y))) z = _
  rw [fderiv_const_smul_field,Pi.smul_apply,fderiv_comp_smul,fderiv_sub hu hq,smul_smul]
  congr 1
  field_simp

theorem actual_normalized_residual_drift_term_four {u q : E → ℝ} {R a : ℝ}
    (hR : 0 < R) {z : E} (hu : DifferentiableAt ℝ u (R • z))
    (hq : DifferentiableAt ℝ q (R • z)) (v : E) :
    fderiv ℝ (normalizedScalarResidualTwo u q R a) z (R • v) =
      a⁻¹*(fderiv ℝ u (R • z) v-fderiv ℝ q (R • z) v) := by
  rw [actual_normalized_residual_fderiv_four hR hu hq]
  simp only [_root_.smul_apply,_root_.sub_apply,map_smul,smul_eq_mul]
  field_simp

theorem actual_normalized_residual_drift_equation_four {U : Set E} (hU : IsOpen U)
    {A : E → Mat} {b : E → E} {f u q : E → ℝ} {R a : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u U) (hq : IsQuadraticPolynomial q)
    (heq : ∀ x ∈ U, (∑ i, ∑ j, A x i j*euclideanHessian u x i j)+
      fderiv ℝ u x (b x) = -f x) :
    ∀ z, R • z ∈ U →
      (∑ i, ∑ j, A (R • z) i j*euclideanHessian (normalizedScalarResidualTwo u q R a) z i j)+
        fderiv ℝ (normalizedScalarResidualTwo u q R a) z (R • b (R • z)) =
      -actualFlatDriftResidualSourceFour A b f q R a z := by
  intro z hz
  have hs : ∀ x ∈ U, (∑ i, ∑ j, A x i j*euclideanHessian u x i j) =
      -(f x+fderiv ℝ u x (b x)) := by
    intro x hx
    linarith [heq x hx]
  rw [actual_normalized_residual_equation_four hU hR hu hq hs z hz,
    actual_normalized_residual_drift_term_four hR
      ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      ((IsQuadraticPolynomial_contDiff hq 2).differentiable (by norm_num)).differentiableAt]
  simp only [actualFlatResidualSourceFour,actualFlatDriftResidualSourceFour]
  ring

end PowerConvexity
