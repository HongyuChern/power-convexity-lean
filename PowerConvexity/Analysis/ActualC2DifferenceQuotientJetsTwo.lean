import PowerConvexity.Analysis.ActualC2SecantFluxTwo
import CHS.Calculus.AffinePullback
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual line difference quotients and their C2 jet identities

All quotients are formed from the given function itself.  The mean-value
bound is uniform in the nonzero increment and only uses a bound for the
actual derivative on the convex set containing the two points.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def actualLineDifferenceQuotientTwo (f : E → F) (v : E) (h : ℝ) (x : E) : F :=
  h⁻¹ • (f (x+h • v)-f x)

theorem actual_line_difference_quotient_tendsto_two
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    Tendsto (fun h => actualLineDifferenceQuotientTwo f v h x) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ f x v)) :=
  (hf.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero

theorem actual_line_difference_quotient_norm_le_two
    {f : E → F} {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) {M : ℝ}
    (hb : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ M)
    {x v : E} {h : ℝ} (hh : h ≠ 0) (hx : x ∈ S) (hxv : x+h • v ∈ S) :
    ‖actualLineDifferenceQuotientTwo f v h x‖ ≤ M*‖v‖ := by
  have he := hS.norm_image_sub_le_of_norm_fderiv_le hf hb hx hxv
  change ‖h⁻¹ • (f (x+h • v)-f x)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  have hc := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (abs_nonneg h))
  have hdist : ‖x+h • v-x‖=|h| *‖v‖ := by simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  rw [hdist] at hc
  calc
    _ ≤ |h|⁻¹*(M*(|h| *‖v‖)) := hc
    _ = _ := by field_simp [abs_ne_zero.mpr hh]

/-- The genuine Euclidean vector associated with the coordinate values of a covector. -/
def actualCovectorVectorTwo : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ({ toFun := fun L => WithLp.toLp 2 (fun i => L (EuclideanSpace.single i 1))
     map_add' := by intro L K; ext i; rfl
     map_smul' := by intro r L; ext i; rfl } : (E →L[ℝ] ℝ) →ₗ[ℝ] E).toContinuousLinearMap

theorem actual_covector_vector_fderiv_two (u : E → ℝ) (x : E) :
    actualCovectorVectorTwo (fderiv ℝ u x)=smoothGradField u x := rfl

theorem actual_fderiv_translate_two {u : E → ℝ} {x d : E}
    (hu : DifferentiableAt ℝ u (x+d)) :
    fderiv ℝ (fun y => u (y+d)) x=fderiv ℝ u (x+d) := by
  have hh := hu.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const d)
  simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hh.fderiv

theorem actual_complex_hessian_translate_two {u : E → ℝ} {x d : E}
    (hu : ContDiffAt ℝ 2 u (x+d)) :
    complexHessian realDirections imagDirections (fun y => u (y+d)) x=
      complexHessian realDirections imagDirections u (x+d) := by
  have h := complexHessian_comp_affine (ContinuousLinearMap.id ℝ E) d
    (x := x) (by simpa only [ContinuousLinearMap.id_apply,add_comm] using hu)
    realDirections imagDirections
  simpa only [ContinuousLinearMap.id_apply,add_comm] using h

theorem actual_midpoint_translated_cofactor_two {u : E → ℝ} {x d : E}
    (hu : ContDiffAt ℝ 2 u x) (hud : ContDiffAt ℝ 2 u (x+d)) :
    complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+u (y+d))) x=
      (1/2 : ℝ) • (complexCofactorCoeff u x+complexCofactorCoeff u (x+d)) := by
  have htrans : ContDiffAt ℝ 2 (fun y => u (y+d)) x :=
    hud.comp x (contDiffAt_id.add contDiffAt_const)
  change actualRealWeightLinearTwo (actualAdjugateLinearTwo
    (complexHessian realDirections imagDirections (fun y => (1/2 : ℝ)*(u y+u (y+d))) x))=_
  rw [complexHessian_const_mul,complexHessian_add hu htrans,actual_complex_hessian_translate_two hud,
    map_smul,map_add,map_smul,map_add]
  rfl

theorem actual_difference_gradient_quotient_two {u : E → ℝ} {x d : E}
    (hu : DifferentiableAt ℝ u x) (hud : DifferentiableAt ℝ u (x+d)) (h : ℝ) :
    h⁻¹ • smoothGradField (fun y => u (y+d)-u y) x=
      actualCovectorVectorTwo (h⁻¹ • (fderiv ℝ u (x+d)-fderiv ℝ u x)) := by
  rw [← actual_covector_vector_fderiv_two,map_smul]
  congr 1
  have ht : DifferentiableAt ℝ (fun y => u (y+d)) x := by
    simpa only [Function.comp_def,id_eq] using hud.comp x (differentiableAt_id.add_const d)
  rw [fderiv_fun_sub ht hu,actual_fderiv_translate_two hud]

end PowerConvexity
