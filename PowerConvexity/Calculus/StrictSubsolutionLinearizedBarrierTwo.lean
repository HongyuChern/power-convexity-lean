import PowerConvexity.Algebra.MinkowskiDeterminantTwo
import PowerConvexity.Calculus.DirectionalDerivativeBoundaryMaximum
import PowerConvexity.Analysis.CompactPositiveScaling
import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # A global strict subsolution gives a uniform negative linearized barrier

The strict constant is chosen from the actual barrier before the unknown
solution. This is a preparatory estimate for mixed boundary derivatives, not
the mixed derivative estimate itself.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem two_sqrt_det_le_trace_quotient_det_one_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hAd : A.det = 1) (hB : B.PosSemidef) :
    2*Real.sqrt B.det.re ≤ (B*A⁻¹).trace.re := by
  obtain ⟨Q,hQ,hQA⟩ := exists_complex_normalization hA
  let C := Q*B*Q.conjTranspose
  have hC : C.PosSemidef := hB.mul_mul_conjTranspose_same Q
  have hq : Complex.normSq Q.det = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det.re) hQA
    rw [determinant_complex_congruence,hAd,Matrix.det_one] at hh
    simpa only [mul_one,Complex.ofReal_re,Complex.one_re] using hh
  have hCd : C.det.re = B.det.re := by
    dsimp only [C]
    rw [determinant_complex_congruence,hq]
    simp
  have hCt : C.trace = (B*A⁻¹).trace := by
    have hh := trace_congruence_quotient Q B A hQ
    rw [hQA,inv_one,Matrix.mul_one] at hh
    exact hh
  have hh := two_sqrt_det_re_le_trace hC
  rwa [hCd,hCt] at hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem strict_subsolution_linearized_barrier_bound_two
    (a b : Fin 2 → E) {u w : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hw : ContDiffAt ℝ 2 w x)
    (hup : (complexHessian a b u x).PosDef)
    (hud : (complexHessian a b u x).det = 1)
    (hwp : (complexHessian a b w x).PosSemidef) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => u y-w y) x) ≤
        -2*(Real.sqrt (complexHessian a b w x).det.re-1) := by
  have hbound := two_sqrt_det_le_trace_quotient_det_one_two hup hud hwp
  have hself := complexHessianContraction_self_eq_card hu a b
    (by rw [hud]; exact one_ne_zero)
  have hwtrace : complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian w x) = ((complexHessian a b w x)*(complexHessian a b u x)⁻¹).trace.re := by
    rw [← complexHessianContraction_pairing a b _ hw,complex_contraction_eq_trace hw]
  rw [realHessian_sub_at hu hw,
    map_sub (complexHessianContraction a b (complexHessian a b u x)⁻¹)
      (realHessian u x) (realHessian w x),hself,hwtrace]
  norm_num at *
  linarith

theorem strict_subsolution_uniform_linearized_barrier_two
    (a b : Fin 2 → E) {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ closure U, (1 : ℂ) < (complexHessian a b w x).det) :
    ∃ eps > 0, ∀ u : E → ℝ, ContDiffOn ℝ 2 u U →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (complexHessian a b u x).det = 1) →
      ∀ x ∈ U, complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realHessian (fun y => u y-w y) x) ≤ -eps := by
  let d : E → ℝ := fun x => Real.sqrt (complexHessian a b w x).det.re-1
  have hdc : Continuous d := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt.comp
      (complexHessian_continuousAt_of_C2 a b hw.contDiffAt)).sqrt).sub continuousAt_const
  have hdpos (x : E) (hx : x ∈ closure U) : 0 < d x := by
    have hh : 1 < (complexHessian a b w x).det.re := by
      simpa only [Complex.one_re] using (Complex.lt_def.mp (hwd x hx)).1
    have hs := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (1 : ℝ)) hh
    dsimp only [d]
    simpa only [Real.sqrt_one,sub_pos] using hs
  obtain ⟨c,hc,hcd⟩ := exists_uniform_square_scaling_gt_one hK hdc hdpos
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hc2 : 0 < c^2 := sq_pos_of_pos hcpos
  refine ⟨2/c^2,div_pos (by norm_num) hc2,?_⟩
  intro u hu hup hud x hx
  have hh := strict_subsolution_linearized_barrier_bound_two a b
    (hu.contDiffAt (hU.mem_nhds hx)) hw.contDiffAt (hup x hx) (hud x hx)
    (hwp x (subset_closure hx)).posSemidef
  have hd : 2/c^2 < 2*d x := (div_lt_iff₀ hc2).mpr (by nlinarith [hcd x (subset_closure hx)])
  change _ ≤ -2*d x at hh
  linarith

end PowerConvexity
