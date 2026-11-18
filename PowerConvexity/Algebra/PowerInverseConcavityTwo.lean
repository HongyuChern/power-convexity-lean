import PowerConvexity.Algebra.CovectorLiftTwo

/-! # Monotonicity and concavity of the inverse-Hessian power equation in dimension two -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder
namespace PowerConvexity

noncomputable def powerInverseValueTwo (p : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ((covectorValueTwo p X).re+Real.sqrt (covectorLiftTwo p X).det.re)/2

theorem powerInverseValueTwo_eq_radical (p : Fin 2 → ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X.PosSemidef) :
    powerInverseValueTwo p X = ((covectorValueTwo p X).re+
      Real.sqrt ((covectorValueTwo p X).re^2+X.det.re))/2 := by
  have hi : (covectorValueTwo p X).im = 0 := (Complex.nonneg_iff.mp (covectorValueTwo_nonneg p hX)).2.symm
  simp only [powerInverseValueTwo,covectorLiftTwo_det,Complex.add_re,pow_two,Complex.mul_re,hi,mul_zero,sub_zero]
  rw [add_comm X.det.re]

theorem powerInverseValueTwo_add_superadditive (p : Fin 2 → ℂ)
    {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosDef) (hY : Y.PosSemidef) :
    powerInverseValueTwo p X+powerInverseValueTwo p Y ≤ powerInverseValueTwo p (X+Y) := by
  have hh := sqrt_det_re_add_superadditive_two (covectorLiftTwo_posDef p hX) (covectorLiftTwo_posSemidef p hY)
  simp only [powerInverseValueTwo,covectorValueTwo_add,covectorLiftTwo_add,Complex.add_re]
  linarith

theorem powerInverseValueTwo_mono (p : Fin 2 → ℂ)
    {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosDef) (hYX : (Y-X).PosSemidef) :
    powerInverseValueTwo p X ≤ powerInverseValueTwo p Y := by
  have ht : (covectorValueTwo p X).re ≤ (covectorValueTwo p Y).re := by
    have hh := (Complex.nonneg_iff.mp (covectorValueTwo_nonneg p hYX)).1
    have he : covectorValueTwo p Y = covectorValueTwo p X+covectorValueTwo p (Y-X) := by
      rw [← covectorValueTwo_add]
      congr 1
      abel
    rw [he,Complex.add_re]
    linarith
  have hL : (covectorLiftTwo p Y-covectorLiftTwo p X).PosSemidef := by
    have he : covectorLiftTwo p Y-covectorLiftTwo p X = covectorLiftTwo p (Y-X) := by
      have ha := covectorLiftTwo_add p X (Y-X)
      have hb : X+(Y-X) = Y := by abel
      rw [hb] at ha
      rw [ha]
      abel
    rw [he]
    exact covectorLiftTwo_posSemidef p hYX
  have hd := det_re_mono_of_posSemidef_sub_two (covectorLiftTwo_posDef p hX) hL
  have hs := Real.sqrt_le_sqrt hd
  dsimp only [powerInverseValueTwo]
  linarith

theorem powerInverseValueTwo_real_smul (p : Fin 2 → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    powerInverseValueTwo p ((c:ℂ) • X) = c*powerInverseValueTwo p X := by
  have he : ((c:ℂ) • covectorLiftTwo p X).det.re = c^2*(covectorLiftTwo p X).det.re := by
    rw [Matrix.det_smul]
    norm_num only [Fintype.card_fin,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [powerInverseValueTwo,covectorValueTwo_smul,covectorLiftTwo_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,he]
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]
  ring

theorem powerInverseValueTwo_weighted_concave (p : Fin 2 → ℂ)
    {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    a*powerInverseValueTwo p X+b*powerInverseValueTwo p Y ≤
      powerInverseValueTwo p ((a:ℂ) • X+(b:ℂ) • Y) := by
  have hac : (0:ℂ) < (a:ℂ) := by exact_mod_cast ha
  have hbc : (0:ℂ) ≤ (b:ℂ) := by exact_mod_cast hb
  have hh := powerInverseValueTwo_add_superadditive p (hX.smul hac) (hY.posSemidef.smul hbc)
  simpa only [powerInverseValueTwo_real_smul p ha.le,powerInverseValueTwo_real_smul p hb] using hh

end PowerConvexity
