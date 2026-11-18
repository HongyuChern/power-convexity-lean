import PowerConvexity.Calculus.UniformAffineTangencyTwo
import PowerConvexity.Analysis.CompactPositiveScaling

/-! # One quadratic tangency constant on a whole compact regular level set

A global C3 defining function supplies actual second/third derivative bounds
on one containing ball. Its differential has a positive lower bound on the
compact level set. The constants precede every center and unit tangent vector.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance catInstance1 : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance catInstance2 : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance catInstance3 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance catInstance4 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance catInstance5 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance catInstance6 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance catInstance7 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance catInstance8 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_compact_uniform_affine_complex_tangency_two
    (e : Module.Basis (Fin 2) ℂ E) {S : Set E} (hS : IsCompact S)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfS : ∀ x ∈ S, f x = 0) (hDf : ∀ x ∈ S, fderiv ℝ f x ≠ 0) :
    ∃ eta > 0, ∃ C > 0, ∃ M ≥ 0,
      (∀ x ∈ S, eta ≤ ‖fderiv ℝ f x‖) ∧
      ∀ x ∈ S, ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
        ∃ (K : E →L[ℂ] E) (c : E),
          (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
          ∀ y ∈ S, |fderiv ℝ f y (c+K y)| ≤ C*‖y-x‖^2 := by
  have hDn : Continuous (fun y => ‖fderiv ℝ f y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hfy : ContDiffAt ℝ 3 f y := hf.contDiffAt
    exact ((hfy.fderiv_right (m := 2) (by norm_num)).continuousAt).norm
  obtain ⟨d,hd,hds⟩ := exists_uniform_square_scaling_gt_one hS hDn
    (fun x hx => (norm_pos_iff (a := fderiv ℝ f x)).mpr (hDf x hx))
  have hdpos : 0 < d := lt_trans (by norm_num) hd
  let eta : ℝ := 1/d^2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hDlower (x : E) (hx : x ∈ S) : eta ≤ ‖fderiv ℝ f x‖ := by
    apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
    simpa only [mul_comm] using (hds x hx).le
  obtain ⟨Q,hQ⟩ := hS.isBounded.exists_norm_le
  let R : ℝ := max Q 1
  have hR : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hSball (x : E) (hx : x ∈ S) : x ∈ closedBall (0 : E) R := by
    simp only [mem_closedBall,dist_zero_right]
    exact (hQ x hx).trans (le_max_left _ _)
  have hHn : Continuous (fun y => ‖realHessian f y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hfy : ContDiffAt ℝ 3 f y := hf.contDiffAt
    exact (((hfy.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt).norm
  have hTn : Continuous (fun y => ‖fderiv ℝ (realHessian f) y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hfy : ContDiffAt ℝ 3 f y := hf.contDiffAt
    exact ((((hfy.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt).norm
  obtain ⟨A0,hA0⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hHn.continuousOn
  obtain ⟨L0,hL0⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hTn.continuousOn
  let A : ℝ := max A0 0
  let L : ℝ := max L0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hL : 0 ≤ L := le_max_right _ _
  have hHb (y : E) (hy : y ∈ closedBall (0 : E) R) : ‖realHessian f y‖ ≤ A := by
    have hh : |‖realHessian f y‖| ≤ A0 := by simpa only [Real.norm_eq_abs] using hA0 y hy
    exact ((le_abs_self _).trans hh).trans (le_max_left _ _)
  have hTb (y : E) (hy : y ∈ closedBall (0 : E) R) : ‖fderiv ℝ (realHessian f) y‖ ≤ L := by
    have hh : |‖fderiv ℝ (realHessian f) y‖| ≤ L0 := by simpa only [Real.norm_eq_abs] using hL0 y hy
    exact ((le_abs_self _).trans hh).trans (le_max_left _ _)
  obtain ⟨C,hC,hquad⟩ := affine_complex_tangency_uniform_on_closedBall_two
    e hR heta hA hL (fun y _ => hf.contDiffAt) hHb hTb
  refine ⟨eta,heta,C,hC,2*A/eta,by positivity,hDlower,?_⟩
  intro x hx tau htau htangent
  obtain ⟨K,c,htr,hcx,hK,hq⟩ := hquad x (hSball x hx) (hDlower x hx) (hfS x hx)
    tau htau htangent
  exact ⟨K,c,htr,hcx,hK,fun y hy => hq y (hSball y hy) (hfS y hy)⟩

end
end PowerConvexity
