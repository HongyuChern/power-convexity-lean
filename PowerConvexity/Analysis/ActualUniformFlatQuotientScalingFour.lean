import PowerConvexity.Analysis.ActualUniformFlatQuotientDataFour

/-! # Exact equivalence of physical and dilated boundary-slope bounds -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_slope_dilate_point_iff_four {r : ℝ} (hr : 0 < r)
    (N : E) (u : E → ℝ) (lo hi : ℝ) (x : E) :
    (lo*inner ℝ N x ≤ r⁻¹*u (r • x) ∧ r⁻¹*u (r • x) ≤ hi*inner ℝ N x) ↔
      (lo*inner ℝ N (r • x) ≤ u (r • x) ∧ u (r • x) ≤ hi*inner ℝ N (r • x)) := by
  rw [inv_mul_eq_div,le_div_iff₀ hr,div_le_iff₀ hr,inner_smul_right]
  constructor <;> intro hh <;> constructor <;> nlinarith [hh.1,hh.2]

theorem actual_flat_slope_dilate_iff_four {r s : ℝ} (hr : 0 < r)
    (N : E) (u : E → ℝ) (lo hi : ℝ) :
    (∀ x ∈ actualFlatClosedUpperBallFour N (r*s),
      lo*inner ℝ N x ≤ u x ∧ u x ≤ hi*inner ℝ N x) ↔
    (∀ x ∈ actualFlatClosedUpperBallFour N s,
      lo*inner ℝ N x ≤ r⁻¹*u (r • x) ∧ r⁻¹*u (r • x) ≤ hi*inner ℝ N x) := by
  constructor
  · intro hh x hx
    exact (actual_flat_slope_dilate_point_iff_four hr N u lo hi x).mpr
      (hh _ (actual_flat_smul_closedUpperBall_four hr hx))
  · intro hh x hx
    have hz := actual_flat_smul_closedUpperBall_four (inv_pos.mpr hr) hx
    have heR : r⁻¹*(r*s)=s := by field_simp
    rw [heR] at hz
    have hb := (actual_flat_slope_dilate_point_iff_four hr N u lo hi (r⁻¹ • x)).mp (hh _ hz)
    simpa only [smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hb

end PowerConvexity
