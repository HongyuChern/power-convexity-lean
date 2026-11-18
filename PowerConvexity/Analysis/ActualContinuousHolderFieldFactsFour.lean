import PowerConvexity.Analysis.ActualContinuousDomainBoundaryDataFour
import PowerConvexity.Analysis.ActualEllipticClosureFour
import Mathlib.Topology.Instances.Matrix

/-! # Actual continuous Holder fields and pointwise inverse coercivity -/
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

theorem actual_holder_matrix_entries_continuous_four
    {V : Set E} {a : E → Mat} {K alpha : ℝ} (halpha : 0 < alpha)
    (hhold : ∀ x ∈ V, ∀ y ∈ V,
      ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤ K*‖x-y‖^alpha) :
    ∀ i j, ContinuousOn (fun x => a x i j) V := by
  intro i j
  apply actual_local_holder_continuousOn_four (by norm_num : (0 : ℝ) < 1) halpha
  intro x hx y hy _
  rw [Real.norm_eq_abs]
  exact (actual_matrix_difference_entry_bound_four (a x) (a y) i j).trans (hhold x hx y hy)

theorem actual_holder_scalar_continuous_four
    {V : Set E} {f : E → ℝ} {K alpha : ℝ} (halpha : 0 < alpha)
    (hhold : ∀ x ∈ V, ∀ y ∈ V, |f x-f y| ≤ K*‖x-y‖^alpha) :
    ContinuousOn f V := by
  apply actual_local_holder_continuousOn_four (by norm_num : (0 : ℝ) < 1) halpha
  intro x hx y hy _
  simpa only [Real.norm_eq_abs] using hhold x hx y hy

theorem actual_holder_elliptic_inverse_coercivity_pointwise_four
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef) :
    ∀ x ∈ U, ∀ v : E, A.Λ⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (A.a x)⁻¹ v) := by
  have hc : ContinuousOn A.a U := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (ha i))
  have hinv : ContinuousOn (fun x => (A.a x)⁻¹) U := by
    intro x hx
    apply ContinuousAt.comp_continuousWithinAt ?_ (hc x hx)
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hpos x hx).det_pos.ne'
  intro x hx v
  have hfield : ContinuousOn (fun y => inner ℝ v (matMulE (A.a y)⁻¹ v)) U :=
    continuousOn_const.inner (actual_continuous_matrix_action_two
      (fun i j => continuousOn_pi.mp (continuousOn_pi.mp hinv i) j) v)
  exact actual_continuousOn_le_of_ae_two hU continuousOn_const hfield
    (A.coercive_inv.mono (fun y hy => hy v)) x hx

theorem actual_distance_le_twice_holder_power_four {d alpha : ℝ}
    (hd : 0 ≤ d) (hd2 : d ≤ 2) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    d ≤ 2*d^alpha := by
  by_cases hd1 : d ≤ 1
  · have hh := Real.self_le_rpow_of_le_one hd hd1 ha1
    nlinarith [Real.rpow_nonneg hd alpha]
  · have hp := Real.one_le_rpow (le_of_not_ge hd1) ha
    linarith

theorem actual_unit_ball_lipschitz_holder_four
    {Z : Type*} [NormedAddCommGroup Z] {g : E → Z} {K alpha : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hLip : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖g x-g y‖ ≤ K*‖x-y‖) :
    ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖g x-g y‖ ≤ (2*K)*‖x-y‖^alpha := by
  intro x hx y hy
  have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hy1 : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hxy : ‖x-y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have hp := actual_distance_le_twice_holder_power_four (norm_nonneg _) hxy ha ha1
  exact (hLip x hx y hy).trans ((mul_le_mul_of_nonneg_left hp hK).trans_eq (by ring))

end PowerConvexity
