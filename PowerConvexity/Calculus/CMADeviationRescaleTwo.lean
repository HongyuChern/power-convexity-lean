import PowerConvexity.Calculus.SmallParaboloidContactHessianTwo
import CHS.Calculus.AffinePullback

/-! # Exact actual Hessians under ball normalization.
Both factors of the spatial scale cancel the quadratic value scale.
The statements concern actual Frechet and Wirtinger derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def normalizedCMADeviationTwo (c : E) (r m : ℝ) (w : E → ℝ) : E → ℝ :=
  fun z => (r^2)⁻¹*(w (c+r • z)-m)

theorem normalizedCMADeviationTwo_contDiffAt
    {w : E → ℝ} {c x : E} {r m : ℝ} (hw : ContDiffAt ℝ 2 w (c+r • x)) :
    ContDiffAt ℝ 2 (normalizedCMADeviationTwo c r m w) x := by
  exact contDiffAt_const.mul ((hw.comp x (by fun_prop)).sub contDiffAt_const)

theorem normalizedCMADeviationTwo_realHessian
    {w : E → ℝ} {c x : E} {r m : ℝ} (hr : r ≠ 0)
    (hw : ContDiffAt ℝ 2 w (c+r • x)) (v z : E) :
    realHessian (normalizedCMADeviationTwo c r m w) x v z =
      realHessian w (c+r • x) v z := by
  have he : normalizedCMADeviationTwo c r m w =
      fun y => (r^2)⁻¹*w (c+r • y)+(-(r^2)⁻¹*m) := by
    funext y
    dsimp only [normalizedCMADeviationTwo]
    ring
  rw [he,CHS.Calculus.realHessian_add_const,CHS.Calculus.realHessian_const_mul]
  change (r^2)⁻¹*realHessian (fun y => w (c+(r • ContinuousLinearMap.id ℝ E) y)) x v z = _
  rw [realHessian_comp_affine (r • ContinuousLinearMap.id ℝ E) c hw]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul,
    smul_apply,smul_eq_mul]
  calc
    _ = ((r^2)⁻¹*r^2)*realHessian w (c+r • x) v z := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero 2 hr),one_mul]

theorem normalizedCMADeviationTwo_complexHessian
    {w : E → ℝ} {c x : E} {r m : ℝ} (hr : r ≠ 0)
    (hw : ContDiffAt ℝ 2 w (c+r • x)) :
    complexHessian realDirections imagDirections (normalizedCMADeviationTwo c r m w) x =
      complexHessian realDirections imagDirections w (c+r • x) := by
  ext i j
  rw [complexHessian_real_entry (normalizedCMADeviationTwo_contDiffAt hw),
    complexHessian_real_entry hw]
  simp only [normalizedCMADeviationTwo_realHessian hr hw]

end PowerConvexity
