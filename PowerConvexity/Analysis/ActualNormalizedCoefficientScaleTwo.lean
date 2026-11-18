import PowerConvexity.Analysis.ActualLinearCoefficientRegularityTwo
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Choosing a physical scale after freezing the actual coefficient

The bound is linear in the distance to the frozen point.  Thus, after an
affine dilation, it supplies the `epsilon * norm z` bound used by the actual
quadratic iteration.  Continuity alone would not provide this conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualMatrixOperatorTwo : Mat →L[ℝ] (E →L[ℝ] E) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    Matrix.toEuclideanLin.toLinearMap).toContinuousLinearMap

theorem actual_matrix_operator_apply_two (A : Mat) (v : E) :
    actualMatrixOperatorTwo A v = matMulE A v := by
  rfl

theorem actual_matrix_operator_one_two :
    actualMatrixOperatorTwo (1 : Mat) = ContinuousLinearMap.id ℝ E := by
  ext v i
  simp only [actual_matrix_operator_apply_two, matMulE_apply, Matrix.one_mulVec,
    ContinuousLinearMap.id_apply]

theorem actual_C1_coefficient_frozen_Lipschitz_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    {c : E} (hc : c ∈ U) (hfreeze : a c = 1) :
    ∃ r > 0, closedBall c r ⊆ U ∧ ∃ K ≥ 0,
      ∀ x ∈ closedBall c r, ∀ v : E,
        ‖v - matMulE (a x) v‖ ≤ (K * ‖x-c‖) * ‖v‖ := by
  have haC : ContDiffAt ℝ 1 a c := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact (ha i j).contDiffAt (hU.mem_nhds hc)
  have ho : ContDiffAt ℝ 1 (fun x => actualMatrixOperatorTwo (a x)) c :=
    actualMatrixOperatorTwo.contDiff.contDiffAt.comp c haC
  obtain ⟨K,V,hV,hLip⟩ := ho.exists_lipschitzOnWith
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hc))
  have hcb : closedBall c (r/2) ⊆ ball c r :=
    closedBall_subset_ball (by linarith)
  refine ⟨r/2,by positivity,(fun x hx => (hsub (hcb hx)).2),K,K.coe_nonneg,?_⟩
  intro x hx v
  have hxV : x ∈ V := (hsub (hcb hx)).1
  have hcV : c ∈ V := mem_of_mem_nhds hV
  have hn : ‖actualMatrixOperatorTwo (a c) - actualMatrixOperatorTwo (a x)‖ ≤
      K * ‖x-c‖ := by
    have hh := hLip.dist_le_mul c hcV x hxV
    simpa only [dist_eq_norm, norm_sub_rev] using hh
  have he : v - matMulE (a x) v =
      (actualMatrixOperatorTwo (a c) - actualMatrixOperatorTwo (a x)) v := by
    rw [hfreeze,actual_matrix_operator_one_two]
    rfl
  rw [he]
  exact ((actualMatrixOperatorTwo (a c) - actualMatrixOperatorTwo (a x)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg v))

theorem actual_C1_coefficient_small_physical_scale_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    {c : E} (hc : c ∈ U) (hfreeze : a c = 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r > 0, r ≤ 1 ∧ closedBall c (2*r) ⊆ U ∧
      ∀ z ∈ closedBall (0 : E) 1, ∀ v : E,
        ‖v - matMulE (a (c+r • z)) v‖ ≤ (epsilon * ‖z‖) * ‖v‖ := by
  obtain ⟨rho,hrho,hclosed,K,hK,hbound⟩ :=
    actual_C1_coefficient_frozen_Lipschitz_two hU ha hc hfreeze
  let r := min 1 (min (rho/2) (epsilon/(K+1)))
  have hr : 0 < r := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrrho : r ≤ rho/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r ≤ epsilon/(K+1) := (min_le_right _ _).trans (min_le_right _ _)
  have hKr : K*r ≤ epsilon := by
    have hh := (le_div_iff₀ (show 0 < K+1 by linarith)).mp hre
    nlinarith
  have hsub : closedBall c (2*r) ⊆ U :=
    (closedBall_subset_closedBall (by linarith : 2*r ≤ rho)).trans hclosed
  refine ⟨r,hr,hr1,hsub,?_⟩
  intro z hz v
  have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hx : c+r • z ∈ closedBall c rho := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := hbound (c+r • z) hx v
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
  have hsmall : K*(r*‖z‖) ≤ epsilon*‖z‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hKr (norm_nonneg z)]
  exact hh.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg v))

end PowerConvexity
