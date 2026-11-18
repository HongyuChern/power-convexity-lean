import PowerConvexity.Calculus.ChordDefectCalculus
import PowerConvexity.Calculus.ScalarPowerEquation

/-! # No positive interior maximum of the actual square-root chord defect -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus

theorem weighted_trace_contact_impossible {a b A B C K X Y Z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hK : 0 < K) (hgap : C < a*A+b*B)
    (hX : A*X = K) (hY : B*Y = K) (hZ : C*Z = K)
    (hmax : (a*A+b*B)^2*Z-a*A^2*X-b*B^2*Y ≤ 0) : False := by
  let S := a*A+b*B
  have hS : 0 < S := add_pos (mul_pos ha hA) (mul_pos hb hB)
  have hAX : A^2*X = A*K := by calc
    _ = A*(A*X) := by ring
    _ = _ := by rw [hX]
  have hBY : B^2*Y = B*K := by calc
    _ = B*(B*Y) := by ring
    _ = _ := by rw [hY]
  have hmax' : S^2*Z ≤ S*K := by
    change S^2*Z-a*A^2*X-b*B^2*Y ≤ 0 at hmax
    rw [mul_assoc a (A^2) X,hAX,mul_assoc b (B^2) Y,hBY] at hmax
    dsimp [S] at *
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hmax' hC.le
  have hCZ : (S^2*Z)*C = S^2*K := by calc
    _ = S^2*(C*Z) := by ring
    _ = _ := by rw [hZ]
  rw [hCZ] at hm
  have hp : 0 < S*K*(S-C) := mul_pos (mul_pos hS hK) (sub_pos.mpr hgap)
  nlinarith

theorem scalarPower_chordDefect_nonpos_of_localMax
    {u : ℂ → ℝ} {x y : ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : ContDiffAt ℝ 2 u x) (hy : ContDiffAt ℝ 2 u y)
    (hz : ContDiffAt ℝ 2 u (a • x+b • y))
    (hnx : u x < 0) (hny : u y < 0) (hnz : u (a • x+b • y) < 0)
    (hρpos : 0 < ρ)
    (hρx : complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ))
    (hρy : complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u y 0 0 = (ρ:ℂ))
    (hρz : complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u (a • x+b • y) 0 0 = (ρ:ℂ))
    (hm : IsLocalMax (chordDefect a b (powerTransform u)) (x,y)) :
    chordDefect a b (powerTransform u) (x,y) ≤ 0 := by
  let f := powerTransform u
  let z := a • x+b • y
  have hfx := powerTransform_contDiffAt hx hnx
  have hfy := powerTransform_contDiffAt hy hny
  have hfz := powerTransform_contDiffAt hz hnz
  obtain ⟨hDx,hDy⟩ := chordDefect_localMax_gradients ha hb
    (hfx.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
    (hfz.differentiableAt (by norm_num)) hm
  have hgx : scalarGradientSquare f x = scalarGradientSquare f z := by
    unfold scalarGradientSquare
    rw [hDx]
  have hgy : scalarGradientSquare f y = scalarGradientSquare f z := by
    unfold scalarGradientSquare
    rw [hDy]
  have heX := scalarPower_equation hx hnx hρx
  have heY := scalarPower_equation hy hny hρy
  have heZ := scalarPower_equation hz hnz hρz
  change (-f x)*scalarRealTrace f x = 2*ρ+scalarGradientSquare f x at heX
  change (-f y)*scalarRealTrace f y = 2*ρ+scalarGradientSquare f y at heY
  rw [hgx] at heX
  rw [hgy] at heY
  have hA : 0 < -f x := neg_pos.mpr (powerTransform_neg_of_neg hnx)
  have hB : 0 < -f y := neg_pos.mpr (powerTransform_neg_of_neg hny)
  have hC : 0 < -f z := neg_pos.mpr (powerTransform_neg_of_neg hnz)
  have hK : 0 < 2*ρ+scalarGradientSquare f z := by
    nlinarith [scalarGradientSquare_nonneg f z]
  have h1 := chordDefect_localMax_weighted_Hessian a b (-f x) (-f y) hfx hfy hfz hm (1:ℂ)
  have hI := chordDefect_localMax_weighted_Hessian a b (-f x) (-f y) hfx hfy hfz hm Complex.I
  have htrace : (a*(-f x)+b*(-f y))^2*scalarRealTrace f z-
      a*(-f x)^2*scalarRealTrace f x-b*(-f y)^2*scalarRealTrace f y ≤ 0 := by
    unfold scalarRealTrace
    change _ ≤ 0
    dsimp [f,z] at *
    linarith
  by_contra hnot
  have hgap : -f z < a*(-f x)+b*(-f y) := by
    change ¬ (f z-a*f x-b*f y ≤ 0) at hnot
    linarith
  exact weighted_trace_contact_impossible ha hb hA hB hC hK hgap heX heY heZ htrace

end PowerConvexity
