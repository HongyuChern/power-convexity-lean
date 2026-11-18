import PowerConvexity.Algebra.FiniteConeWithDensityErrorTwo
import CHS.Algebra.HessianEntryBounds

/-! # Small paraboloid contact bounds on the actual determinant-one branch.
These are pointwise algebraic estimates for the small-perturbation route.
They do not assert a contact-set measure bound or an interior C2 estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Algebra CHS.Calculus
local notation "J" => Fin 2 ⊕ Fin 2
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem det_one_trace_upper_of_small_scalar_lower_two
    {A : W} (hdet : A.det = 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hlower : (A-((1-a/2 : ℝ) : ℂ) • (1 : W)).PosSemidef) :
    A.trace.re ≤ 2+a := by
  let c : ℝ := 1-a/2
  have hc : 0 < c := by dsimp only [c]; linarith only [ha1]
  have hd : 0 ≤ (A-(c : ℂ) • (1 : W)).det.re :=
    (Complex.nonneg_iff.mp hlower.det_nonneg).1
  have he : (A-(c : ℂ) • (1 : W)).det.re = 1-c*A.trace.re+c^2 := by
    rw [show A-(c : ℂ) • (1 : W) = A+(-(c : ℂ)) • (1 : W) by module,
      det_add_scalar_one_two,hdet]
    simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.neg_re,
      Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,
      sub_zero,pow_two]
    ring
  rw [he] at hd
  have haa : a^2 ≤ a := by nlinarith only [ha,ha1]
  have hcbd : 1+c^2 ≤ c*(2+a) := by
    dsimp only [c]
    nlinarith only [ha,haa]
  exact le_of_mul_le_mul_left (by linarith only [hd,hcbd]) hc

theorem real_matrix_entry_abs_le_trace_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (hH : H.PosSemidef) (i j : ι) : |H i j| ≤ H.trace := by
  have hc := (real_matrix_posSemidef_iff_complexification hH.isHermitian).mp hH
  have hh := norm_entry_le_trace_re hc i j
  simpa only [Matrix.map_apply,Complex.norm_real,Real.norm_eq_abs,
    Matrix.trace,Matrix.diag_apply,Complex.re_sum,Complex.ofReal_re] using hh

theorem small_paraboloid_lower_contact_entry_bound_two
    {H : V} {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hcontact : (H+a • (1 : V)).PosSemidef)
    (hdet : (1+complexProjection H).det = 1) :
    ∀ i j : J, |H i j| ≤ 9*a := by
  let B : V := H+a • (1 : V)
  have hD : ((1+complexProjection H)-((1-a/2 : ℝ) : ℂ) • (1 : W)).PosSemidef := by
    have hh := complexProjection_posSemidef hcontact
    have he : complexProjection (H+a • (1 : V)) =
        (1+complexProjection H)-((1-a/2 : ℝ) : ℂ) • (1 : W) := by
      rw [complexProjection_add_two,complexProjection_smul,complexProjection_one_two,smul_smul]
      ext i j
      simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
        Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,
        Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
      ring
    rwa [he] at hh
  have hT := det_one_trace_upper_of_small_scalar_lower_two hdet ha ha1 hD
  have htrace : (1+complexProjection H).trace.re = 2+(complexProjection H).trace.re := by
    norm_num [Matrix.trace_add,Matrix.trace_one]
  have hHT : H.trace ≤ 4*a := by
    have hproj := four_complexProjection_trace_re H
    rw [htrace] at hT
    linarith only [hproj,hT]
  have hBT : B.trace ≤ 8*a := by
    dsimp only [B]
    rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one]
    norm_num only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,smul_eq_mul]
    linarith only [hHT]
  intro i j
  have hb := real_matrix_entry_abs_le_trace_of_posSemidef hcontact i j
  have he : H i j = B i j-a*(1 : V) i j := by simp only [B,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring
  have hi : |a*(1 : V) i j| ≤ a := by
    by_cases hij : i = j <;> simp [Matrix.one_apply,hij,abs_of_nonneg ha,ha]
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hb hi).trans (by change B.trace+a ≤ 9*a; linarith only [hBT]))

theorem small_paraboloid_upper_contact_entry_bound_two
    {H : V} {a : ℝ} (ha : 0 ≤ a)
    (hcontact : (a • (1 : V)-H).PosSemidef)
    (hpsh : (1+complexProjection H).PosSemidef)
    (hdet : (1+complexProjection H).det = 1) :
    ∀ i j : J, |H i j| ≤ 5*a := by
  let B : V := a • (1 : V)-H
  have hT := two_sqrt_det_re_le_trace hpsh
  rw [hdet] at hT
  norm_num [Matrix.trace_add,Matrix.trace_one] at hT
  have hHT : 0 ≤ H.trace := by
    have hp := four_complexProjection_trace_re H
    linarith only [hT,hp]
  have hBT : B.trace ≤ 4*a := by
    dsimp only [B]
    rw [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one]
    norm_num only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,smul_eq_mul]
    linarith only [hHT]
  intro i j
  have hb := real_matrix_entry_abs_le_trace_of_posSemidef hcontact i j
  have he : H i j = a*(1 : V) i j-B i j := by simp only [B,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]; ring
  have hi : |a*(1 : V) i j| ≤ a := by
    by_cases hij : i = j <;> simp [Matrix.one_apply,hij,abs_of_nonneg ha,ha]
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hi hb).trans (by change a+B.trace ≤ 5*a; linarith only [hBT]))

end PowerConvexity
