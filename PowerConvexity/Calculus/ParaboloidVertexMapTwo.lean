import PowerConvexity.Calculus.CMADeviationContactsTwo
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-! # The actual small-paraboloid vertex map and its measure bound.
The derivative is computed from the actual Frechet Hessian. The image
estimate uses the checked change-of-variables inequality, without an
injectivity assumption. The set in this theorem is any measurable set
of actual lower contacts; no covering or Harnack result is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric MeasureTheory InnerProductSpace
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

def paraboloidVertexMapTwo (a : ℝ) (w : E → ℝ) (x : E) : E :=
  x+a⁻¹ • gradient w x

def paraboloidVertexDerivativeTwo (a : ℝ) (w : E → ℝ) (x : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E+a⁻¹ • continuousLinearMapOfBilin (realHessian w x)

theorem paraboloidVertexMapTwo_hasFDerivAt
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) (a : ℝ) :
    HasFDerivAt (paraboloidVertexMapTwo a w) (paraboloidVertexDerivativeTwo a w x) x := by
  have hd : HasFDerivAt (fderiv ℝ w) (realHessian w x) x :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  let L := (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg := L.hasFDerivAt.comp x hd
  exact (hasFDerivAt_id x).add (hg.const_smul a⁻¹)

theorem realHessian_sharp_norm_le (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖continuousLinearMapOfBilin H‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro v
  simpa only [continuousLinearMapOfBilin,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map] using H.le_opNorm v

theorem paraboloidVertexDerivativeTwo_norm_le_of_small_lower_contact
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) :
    ‖paraboloidVertexDerivativeTwo a w x‖ ≤ 145 := by
  have hH := (realHessian_sharp_norm_le (realHessian w x)).trans
    (actual_small_semiconvex_hessian_bound_two hw ha.le ha1 hdet hcontact)
  calc
    ‖paraboloidVertexDerivativeTwo a w x‖ ≤
        ‖ContinuousLinearMap.id ℝ E‖+‖a⁻¹ • continuousLinearMapOfBilin (realHessian w x)‖ :=
      norm_add_le _ _
    _ = 1+a⁻¹*‖continuousLinearMapOfBilin (realHessian w x)‖ := by
      rw [ContinuousLinearMap.norm_id,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    _ ≤ 1+a⁻¹*(144*a) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hH (inv_pos.mpr ha).le)
    _ = 145 := by field_simp; ring

theorem exists_universal_small_lower_contact_image_measure_bound_two :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : E → ℝ) (S : Set E) (a : ℝ),
      MeasurableSet S → 0 < a → a ≤ 1 →
      (∀ x ∈ S, ContDiffAt ℝ 2 w x) →
      (∀ x ∈ S, (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ S, ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) →
      volume (paraboloidVertexMapTwo a w '' S) ≤ ENNReal.ofReal K*volume S := by
  have hcd : Continuous (fun A : E →L[ℝ] E => A.det) := ContinuousLinearMap.continuous_det
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) 145).exists_bound_of_continuousOn
    hcd.continuousOn
  let K : ℝ := max B 0+1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro w S a hS ha ha1 hw hdet hcontact
  have hderiv (x : E) (hx : x ∈ S) :
      HasFDerivWithinAt (paraboloidVertexMapTwo a w)
        (paraboloidVertexDerivativeTwo a w x) S x :=
    (paraboloidVertexMapTwo_hasFDerivAt (hw x hx) a).hasFDerivWithinAt
  have hbound (x : E) (hx : x ∈ S) :
      ENNReal.ofReal |(paraboloidVertexDerivativeTwo a w x).det| ≤ ENNReal.ofReal K := by
    apply ENNReal.ofReal_le_ofReal
    have hb := hB (paraboloidVertexDerivativeTwo a w x) (by
      simpa only [mem_closedBall,dist_zero_right] using
        paraboloidVertexDerivativeTwo_norm_le_of_small_lower_contact
          (hw x hx) ha ha1 (hdet x hx) (hcontact x hx))
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by dsimp only [K]; linarith only [le_max_left B 0])
  calc
    volume (paraboloidVertexMapTwo a w '' S) ≤
        ∫⁻ x in S, ENNReal.ofReal |(paraboloidVertexDerivativeTwo a w x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hS hderiv
    _ ≤ ∫⁻ _x in S, ENNReal.ofReal K :=
      setLIntegral_mono' hS hbound
    _ = ENNReal.ofReal K*volume S := by simp

end PowerConvexity
