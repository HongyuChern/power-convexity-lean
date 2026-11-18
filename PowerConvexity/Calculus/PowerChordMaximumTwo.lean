import PowerConvexity.Calculus.ChordComplexContact
import PowerConvexity.Calculus.PowerMatrixRecovery

/-! # No positive interior two-point maximum for the actual power transform

A supplementary direct route. All gradients and complex Hessians are actual
Wirtinger derivatives; the equal-gradient and contact conditions are derived.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem power_chordDefect_nonpos_of_localMax_two
    {u : E → ℝ} {x y : E} {a b : ℝ} (e k : Fin 2 → E)
    (ha : 0 < a) (hb : 0 < b)
    (hx : ContDiffAt ℝ 2 u x) (hy : ContDiffAt ℝ 2 u y)
    (hz : ContDiffAt ℝ 2 u (a • x+b • y))
    (hnx : u x < 0) (hny : u y < 0) (hnz : u (a • x+b • y) < 0)
    (hAx : (complexHessian e k u x).PosDef)
    (hAy : (complexHessian e k u y).PosDef)
    (hAz : (complexHessian e k u (a • x+b • y)).PosDef)
    (hdetx : (complexHessian e k u x).det = 1)
    (hdety : (complexHessian e k u y).det = 1)
    (hdetz : (complexHessian e k u (a • x+b • y)).det = 1)
    (hm : IsLocalMax (chordDefect a b (powerTransform u)) (x,y)) :
    chordDefect a b (powerTransform u) (x,y) ≤ 0 := by
  let f := powerTransform u
  let z := a • x+b • y
  let X := (complexHessian e k f x)⁻¹
  let Y := (complexHessian e k f y)⁻¹
  let Z := (complexHessian e k f z)⁻¹
  let p := complexGradient e k f z
  let S := (a:ℂ) • X+(b:ℂ) • Y
  have hfx : ContDiffAt ℝ 2 f x := powerTransform_contDiffAt hx hnx
  have hfy : ContDiffAt ℝ 2 f y := powerTransform_contDiffAt hy hny
  have hfz : ContDiffAt ℝ 2 f z := powerTransform_contDiffAt hz hnz
  have hpx : (complexHessian e k f x).PosDef :=
    (power_mixed_posDef_iff_modifiedA hx hnx e k).mpr (modifiedA_posDef e k hnx hAx)
  have hpy : (complexHessian e k f y).PosDef :=
    (power_mixed_posDef_iff_modifiedA hy hny e k).mpr (modifiedA_posDef e k hny hAy)
  have hpz : (complexHessian e k f z).PosDef :=
    (power_mixed_posDef_iff_modifiedA hz hnz e k).mpr (modifiedA_posDef e k hnz hAz)
  obtain ⟨hDx,hDy⟩ := chordDefect_localMax_gradients ha hb
    (hfx.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
    (hfz.differentiableAt (by norm_num)) hm
  have hgpX : complexGradient e k f x = p := by
    funext i
    dsimp only [p]
    rw [complexGradient_real_entry (hfx.differentiableAt (by norm_num)),
      complexGradient_real_entry (hfz.differentiableAt (by norm_num)),hDx]
  have hgpY : complexGradient e k f y = p := by
    funext i
    dsimp only [p]
    rw [complexGradient_real_entry (hfy.differentiableAt (by norm_num)),
      complexGradient_real_entry (hfz.differentiableAt (by norm_num)),hDy]
  have heX : powerInverseValueTwo p X = -f x := by
    have hh := actualPower_inverse_equation_two hx hnx e k hAx hdetx
    change powerInverseValueTwo (complexGradient e k f x) X = -f x at hh
    rwa [hgpX] at hh
  have heY : powerInverseValueTwo p Y = -f y := by
    have hh := actualPower_inverse_equation_two hy hny e k hAy hdety
    change powerInverseValueTwo (complexGradient e k f y) Y = -f y at hh
    rwa [hgpY] at hh
  have heZ : powerInverseValueTwo p Z = -f z := actualPower_inverse_equation_two hz hnz e k hAz hdetz
  have hS : S.PosDef := (hpx.inv.smul (by exact_mod_cast ha : (0:ℂ) < (a:ℂ))).add_posSemidef
    (hpy.inv.posSemidef.smul (by exact_mod_cast hb.le : (0:ℂ) ≤ (b:ℂ)))
  have horder : (Z-S).PosSemidef :=
    chordDefect_localMax_inverse_complex_order a b e k hfx hfy hfz hpx hpy hpz hm
  have hmono := powerInverseValueTwo_mono p hS horder
  have hconc := powerInverseValueTwo_weighted_concave p hpx.inv hpy.inv ha hb.le
  change a*powerInverseValueTwo p X+b*powerInverseValueTwo p Y ≤ powerInverseValueTwo p S at hconc
  rw [heZ] at hmono
  rw [heX,heY] at hconc
  change f z-a*f x-b*f y ≤ 0
  linarith

end PowerConvexity
