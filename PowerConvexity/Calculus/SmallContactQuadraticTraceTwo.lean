import PowerConvexity.Calculus.SmallContactTraceBarrierTwo

/-! # Quadratic trace error at actual small contacts.
The determinant equation improves the previous linear trace error to a
quadratic error. After normalization this error tends to zero, which is
the needed consistency estimate for the limiting Laplace equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem det_one_trace_quadratic_upper_of_small_scalar_lower_two
    {A : W} (hdet : A.det = 1) {a : ℝ} (ha1 : a ≤ 1)
    (hlower : (A-((1-a/2 : ℝ) : ℂ) • (1 : W)).PosSemidef) :
    A.trace.re ≤ 2+a^2/2 := by
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
  have hcbd : 1+c^2 ≤ c*(2+a^2/2) := by
    have hh := mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg a)
    dsimp only [c]
    nlinarith only [hh]
  exact le_of_mul_le_mul_left (by linarith only [hd,hcbd]) hc

theorem small_paraboloid_lower_contact_quadratic_trace_bound_two
    {H : V} {a : ℝ} (ha1 : a ≤ 1)
    (hcontact : (H+a • (1 : V)).PosSemidef)
    (hdet : (1+complexProjection H).det = 1) : H.trace ≤ 2*a^2 := by
  have hh := complexProjection_posSemidef hcontact
  have he : complexProjection (H+a • (1 : V)) =
      (1+complexProjection H)-((1-a/2 : ℝ) : ℂ) • (1 : W) := by
    rw [complexProjection_add_two,complexProjection_smul,complexProjection_one_two,smul_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  rw [he] at hh
  have ht := det_one_trace_quadratic_upper_of_small_scalar_lower_two hdet ha1 hh
  norm_num [Matrix.trace_add,Matrix.trace_one] at ht
  have hp := four_complexProjection_trace_re H
  linarith only [ht,hp]

theorem actual_small_semiconvex_quadratic_trace_bound_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) :
    (realBlockHessian realDirections imagDirections w x).trace ≤ 2*a^2 := by
  apply small_paraboloid_lower_contact_quadratic_trace_bound_two ha1
    (realBlockHessian_scalar_lower_posSemidef_two hw hcontact)
  rwa [complexProjection_realBlockHessian hw]

theorem actual_normalized_CMA_lower_contact_trace_two
    {w p : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) (hp : ContDiffAt ℝ 2 p x)
    {ε K : ℝ} (hε : 0 < ε) (hsmall : ε*K ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hlower : ∀ v : E, -(K*‖v‖^2) ≤ realHessian p x v v)
    (hm : IsLocalMin (fun y => w y-ε*p y) x) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 2*ε*K^2 := by
  have horder := realHessian_le_of_isLocalMin_sub hw (contDiffAt_const.mul hp) hm
  have hlow (v : E) : -(ε*K*‖v‖^2) ≤ realHessian w x v v := by
    have hh := mul_le_mul_of_nonneg_left (hlower v) hε.le
    have ho := horder v
    rw [CHS.Calculus.realHessian_const_mul] at ho
    change ε*realHessian p x v v ≤ realHessian w x v v at ho
    nlinarith only [hh,ho]
  have ht := actual_small_semiconvex_quadratic_trace_bound_two hw hsmall hdet hlow
  have htr : ε*(realBlockHessian realDirections imagDirections p x).trace ≤
      (realBlockHessian realDirections imagDirections w x).trace := by
    simp only [Matrix.trace,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    simpa only [realBlockHessian,Matrix.diag_apply,CHS.Calculus.realHessian_const_mul,
      ContinuousLinearMap.smul_apply,smul_eq_mul] using
      horder (Sum.elim realDirections imagDirections i)
  apply le_of_mul_le_mul_left (a := ε) _ hε
  nlinarith only [htr,ht]

theorem actual_normalized_CMA_upper_contact_trace_two
    {w p : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) (hp : ContDiffAt ℝ 2 p x)
    {ε : ℝ} (hε : 0 < ε)
    (hpsh : (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hm : IsLocalMin (fun y => ε*p y-w y) x) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  have horder := realHessian_le_of_isLocalMin_sub (contDiffAt_const.mul hp) hw hm
  have ht := two_sqrt_det_re_le_trace hpsh
  rw [hdet] at ht
  norm_num [Matrix.trace_add,Matrix.trace_one] at ht
  have hpj := four_complexProjection_trace_re (realBlockHessian realDirections imagDirections w x)
  rw [complexProjection_realBlockHessian hw] at hpj
  have htr : (realBlockHessian realDirections imagDirections w x).trace ≤
      ε*(realBlockHessian realDirections imagDirections p x).trace := by
    simp only [Matrix.trace,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    simpa only [realBlockHessian,Matrix.diag_apply,CHS.Calculus.realHessian_const_mul,
      ContinuousLinearMap.smul_apply,smul_eq_mul] using
      horder (Sum.elim realDirections imagDirections i)
  have hn : 0 ≤ ε*(realBlockHessian realDirections imagDirections p x).trace := by
    linarith only [ht,hpj,htr]
  exact (mul_nonneg_iff_of_pos_left hε).mp hn

end PowerConvexity
