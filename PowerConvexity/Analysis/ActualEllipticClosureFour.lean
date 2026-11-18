import PowerConvexity.Analysis.ActualUniformNormalizationBoundsTwo

/-! # The original ellipticity constants on the actual closure -/
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

theorem actual_elliptic_bounds_on_closure_four {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closure U)) :
    ∀ x ∈ closure U, ∀ v : E,
      A.lam*‖v‖^2 ≤ inner ℝ v (matMulE (A.a x) v) ∧
        inner ℝ v (matMulE (A.a x) v) ≤ A.Λ*‖v‖^2 := by
  have hinside := actual_elliptic_bounds_pointwise_two hU A (fun i j => (hA i j).mono subset_closure)
  intro x hx v
  have hc : ContinuousOn (fun y => inner ℝ v (matMulE (A.a y) v)) (closure U) :=
    continuousOn_const.inner (actual_continuous_matrix_action_two hA v)
  exact ⟨le_on_closure (fun y hy => (hinside y hy v).1) continuousOn_const hc hx,
    le_on_closure (fun y hy => (hinside y hy v).2) hc continuousOn_const hx⟩

theorem actual_positive_elliptic_coefficient_on_closure_four {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closure U))
    (hpos : ∀ x ∈ U, (A.a x).PosDef) : ∀ x ∈ closure U, (A.a x).PosDef := by
  have hb := actual_elliptic_bounds_on_closure_four hU A hA
  intro x hx
  have hherm : (A.a x).IsHermitian := by
    have hc : ContinuousOn A.a (closure U) := continuousOn_pi.mpr (fun i =>
      continuousOn_pi.mpr (fun j => hA i j))
    have he : EqOn (fun y => (A.a y)ᴴ) A.a U := fun y hy => (hpos y hy).isHermitian
    have hcT : ContinuousOn (fun y => (A.a y)ᴴ) (closure U) := by fun_prop
    exact he.of_subset_closure hcT hc subset_closure Subset.rfl hx
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
  intro v hv
  let w : E := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    have hh := congrArg (fun z : E => z.ofLp) hz
    change v=0 at hh
    exact hh
  have hp : 0 < inner ℝ w (matMulE (A.a x) w) :=
    (mul_pos A.hlam (sq_pos_of_pos (norm_pos_iff.mpr hw))).trans_le (hb x hx w).1
  simpa [w,PiLp.inner_apply,Real.inner_apply,matMulE_apply,dotProduct,mul_comm] using hp

end PowerConvexity
