import PowerConvexity.Analysis.ActualPositiveBoundaryBarrierH01Two

/-! # Actual signed zero-trace data controlled by a positive boundary barrier
The signed function is the difference of two genuine positive C1 boundary
barriers; both are approximated in H1 by the previously constructed cutoffs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_memH01_of_smooth_positive_barrier_domination_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {p q : E → ℝ} (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q)
    (hpos : ∀ x ∈ U, 0 < q x)
    (hp0 : ∀ x ∈ frontier U, p x=0) (hq0 : ∀ x ∈ frontier U, q x=0)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ U, |p x| ≤ C*q x) :
    MemH01 p U := by
  let r : E → ℝ := fun x => (C+1)*q x
  have hr : ContDiff ℝ 1 r := contDiff_const.mul hq
  have hrpos (x : E) (hx : x ∈ U) : 0 < r x := mul_pos (by linarith) (hpos x hx)
  have hr0 (x : E) (hx : x ∈ frontier U) : r x=0 := by simp only [r,hq0 x hx,mul_zero]
  have hrH := actual_positive_boundary_barrier_memH01_two hU hK hr hrpos hr0
  have hrpH : MemH01 (fun x => r x+p x) U :=
    actual_positive_boundary_barrier_memH01_two hU hK (hr.add hp) (by
      intro x hx
      have hb := neg_abs_le (p x)
      have hbp := hbound x hx
      have hqp := hpos x hx
      dsimp only [r]
      nlinarith) (by intro x hx; rw [hr0 x hx,hp0 x hx,add_zero])
  have hh := MemW01p.sub hrpH hrH
  simpa only [add_sub_cancel_left] using hh

end PowerConvexity
