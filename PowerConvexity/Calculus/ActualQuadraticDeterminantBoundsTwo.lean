import PowerConvexity.Algebra.TracelessDeterminantCorrectionTwo
import PowerConvexity.Calculus.SmallContactTraceBarrierTwo
import PowerConvexity.Calculus.PoissonIntegralHessianBoundsFour

/-! # Actual norm and trace inputs for determinant correction.
Every matrix is the actual complex Hessian in the fixed real directions.
The determinant bound follows from actual operator-norm bounds and the
zero actual real trace, with the coordinate normalization explicitly checked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_realBlockHessian_entry_le_operator_norm_two (u : E → ℝ) (x : E) (i j : J) :
    |realBlockHessian realDirections imagDirections u x i j| ≤ ‖realHessian u x‖ := by
  have hh := (realHessian u x).le_opNorm₂
    (Sum.elim realDirections imagDirections i) (Sum.elim realDirections imagDirections j)
  simpa only [realBlockHessian,blockDirection_eq_single,EuclideanSpace.norm_single,norm_one,
    mul_one,Real.norm_eq_abs] using hh

theorem complexProjection_real_imag_bound_two {H : Matrix J J ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hH : ∀ i j, |H i j| ≤ K) (i j : Fin 2) :
    |(complexProjection H i j).re| ≤ K ∧ |(complexProjection H i j).im| ≤ K := by
  have haa := abs_le.mp (hH (.inl i) (.inl j))
  have hbb := abs_le.mp (hH (.inr i) (.inr j))
  have hab := abs_le.mp (hH (.inl i) (.inr j))
  have hba := abs_le.mp (hH (.inr i) (.inl j))
  have hs : |H (.inl i) (.inl j)+H (.inr i) (.inr j)| ≤ 2*K :=
    abs_le.mpr ⟨by linarith only [haa.1,hbb.1],by linarith only [haa.2,hbb.2]⟩
  have hd : |H (.inl i) (.inr j)-H (.inr i) (.inl j)| ≤ 2*K :=
    abs_le.mpr ⟨by linarith only [hab.1,hba.2],by linarith only [hab.2,hba.1]⟩
  norm_num [complexProjection,Complex.mul_re,Complex.mul_im]
  constructor <;> linarith

theorem actual_complexHessian_trace_zero_of_real_trace_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x)
    (ht : (realBlockHessian realDirections imagDirections u x).trace = 0) :
    (complexHessian realDirections imagDirections u x).trace = 0 := by
  have hp := four_complexProjection_trace_re (realBlockHessian realDirections imagDirections u x)
  rw [complexProjection_realBlockHessian hu,ht] at hp
  have hA := complexHessian_isHermitian hu realDirections imagDirections
  have hi (i : Fin 2) : (complexHessian realDirections imagDirections u x i i).im = 0 := by
    have hh := congrArg Complex.im (hA.apply i i)
    change -(complexHessian realDirections imagDirections u x i i).im =
      (complexHessian realDirections imagDirections u x i i).im at hh
    linarith
  apply Complex.ext
  · change (complexHessian realDirections imagDirections u x).trace.re = 0
    linarith only [hp]
  · simp only [Matrix.trace,Matrix.diag_apply,Complex.im_sum,hi,Finset.sum_const_zero,Complex.zero_im]

theorem actual_complexHessian_traceless_det_bound_two {u : E → ℝ} {x : E} {K : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hK : 0 ≤ K) (hH : ‖realHessian u x‖ ≤ K)
    (ht : (realBlockHessian realDirections imagDirections u x).trace = 0) :
    -(complexHessian realDirections imagDirections u x).det.re ≤ 3*K^2 := by
  let A := complexHessian realDirections imagDirections u x
  have hA : A.IsHermitian := complexHessian_isHermitian hu realDirections imagDirections
  have hAt : A.trace = 0 := actual_complexHessian_trace_zero_of_real_trace_two hu ht
  have hE (i j : Fin 2) : |(A i j).re| ≤ K ∧ |(A i j).im| ≤ K := by
    have hh := complexProjection_real_imag_bound_two hK
      (fun i j => (actual_realBlockHessian_entry_le_operator_norm_two u x i j).trans hH) i j
    rwa [complexProjection_realBlockHessian hu] at hh
  have htr : (A 0 0).re+(A 1 1).re = 0 := by
    have hh := congrArg Complex.re hAt
    simpa only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,Complex.add_re,Complex.zero_re] using hh
  have h11 : (A 1 1).re = -(A 0 0).re := by linarith only [htr]
  have hd : A.det = (((A 0 0).re*(A 1 1).re-(A 0 1).re^2-(A 0 1).im^2 : ℝ) : ℂ) := by
    conv_lhs => rw [hermitianMatrixTwo_eq_of_isHermitian A hA]
    exact hermitianMatrixTwo_det _ _ _ _
  have hsq {a : ℝ} (ha : |a| ≤ K) : a^2 ≤ K^2 := by
    have hl := abs_le.mp ha
    nlinarith only [mul_nonneg (sub_nonneg.mpr hl.2) (by linarith only [hl.1] : 0 ≤ K+a)]
  change -A.det.re ≤ 3*K^2
  rw [hd,Complex.ofReal_re,h11]
  nlinarith only [hsq (hE 0 0).1,hsq (hE 0 1).1,hsq (hE 0 1).2]

theorem actual_small_Hessian_identity_complex_posDef_two {u : E → ℝ} {x : E} {K : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hH : ‖realHessian u x‖ ≤ K) (hK1 : K ≤ 1) :
    (1+complexHessian realDirections imagDirections u x).PosDef := by
  have hK : 0 ≤ K := (norm_nonneg (realHessian u x)).trans hH
  have hlow (v : E) : -(K*‖v‖^2) ≤ realHessian u x v v := by
    have hh := (realHessian u x).le_opNorm₂ v v
    have hb : ‖realHessian u x v v‖ ≤ K*‖v‖^2 := hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg ‖v‖)])
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)).1
  have hp := complexProjection_posSemidef (realBlockHessian_scalar_lower_posSemidef_two hu hlow)
  rw [complexProjection_add_two,complexProjection_smul,complexProjection_one_two,
    complexProjection_realBlockHessian hu,smul_smul] at hp
  have hp' : (complexHessian realDirections imagDirections u x+
      ((K/2 : ℝ) : ℂ) • (1 : W)).PosSemidef := by
    convert hp using 1 <;> ext i j <;>
      simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,
        Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] <;> ring
  have hc : (0 : ℂ) < ((1-K/2 : ℝ) : ℂ) :=
    Complex.pos_iff.mpr ⟨by simp only [Complex.ofReal_re]; linarith only [hK1],by simp⟩
  have hpos := (Matrix.PosDef.one : (1 : W).PosDef).smul hc
  have he : ((1-K/2 : ℝ) : ℂ) • (1 : W)+
      (complexHessian realDirections imagDirections u x+((K/2 : ℝ) : ℂ) • (1 : W)) =
      1+complexHessian realDirections imagDirections u x := by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Complex.ofReal_sub,Complex.ofReal_one,smul_eq_mul]
    ring
  rw [← he]
  exact hpos.add_posSemidef hp'

end PowerConvexity
