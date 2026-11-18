import PowerConvexity.Calculus.StrictSubsolutionBoundaryComparisonTwo
import PowerConvexity.Calculus.GlobalStrictSubsolutionScalingTwo

/-! # A fixed strict psh potential supplies a genuine small supersolution

Compactness chooses a positive scalar before the unknown solution. Actual
determinant scaling makes the new determinant less than one. Comparison and
differentiation within the true convex closure then bound inward derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_strictPsh_has_small_det_scaling_two
    (a b : Fin 2 → E) {S : Set E} (hS : IsCompact S)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ S, (complexHessian a b w x).PosDef) :
    ∃ c > 0, ∀ x ∈ S,
      (complexHessian a b (fun y => c*w y) x).PosDef ∧
      (complexHessian a b (fun y => c*w y) x).det.re < 1 := by
  let d : E → ℝ := fun x => (complexHessian a b w x).det.re
  have hdc : Continuous d := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (complexHessian_continuousAt_of_C2 a b hw.contDiffAt)
  let F : ℝ × E → ℝ := fun z => 1-z.1^2*d z.2
  have hFc : Continuous F := continuous_const.sub
    ((continuous_fst.pow 2).mul (hdc.comp continuous_snd))
  obtain ⟨c,hc,hsmall⟩ := compact_small_parameter_positive (F := F) hS
    (fun x _ => hFc.continuousAt) (fun x _ => by simp [F])
  refine ⟨c,hc,?_⟩
  intro x hx
  have hscale := complexHessian_const_mul_at hw.contDiffAt c a b (x := x)
  refine ⟨?_,?_⟩
  · rw [hscale]
    exact (hwp x hx).smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  · have he : (complexHessian a b (fun y => c*w y) x).det.re = c^2*d x := by
      rw [hscale,Matrix.det_smul]
      simp [d,Complex.mul_re,Complex.mul_im,pow_two]
    have hh := hsmall c (by simpa only [Real.norm_eq_abs,abs_of_pos hc] using (le_rfl : c ≤ c)) x hx
    change 0 < 1-c^2*d x at hh
    rw [he]
    linarith

theorem strictPsh_uniform_scaled_supersolution_comparison_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef) :
    ∃ c > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (complexHessian a b u x).det = 1) →
      (∀ x ∈ closure U, u x ≤ c*w x) ∧
      ∀ x ∈ frontier U, ∀ y ∈ closure U,
        J.derivative x (y-x) ≤ c*fderiv ℝ w x (y-x) := by
  obtain ⟨c,hc,hscale⟩ := compact_strictPsh_has_small_det_scaling_two a b hK hw hwp
  let W : E → ℝ := fun y => c*w y
  have hW : ContDiff ℝ 2 W := contDiff_const.mul hw
  have hWb : ∀ x ∈ frontier U, W x = 0 := fun x hx => by simp only [W,hwb x hx,mul_zero]
  refine ⟨c,hc,?_⟩
  intro u J hu hub hup hud
  have hle : ∀ x ∈ closure U, u x ≤ W x := by
    apply classical_strict_comparison_two hU hK a b J.continuous_value
      hW.continuous.continuousOn hu hW.contDiffOn hup
    · intro x hx
      rw [hud x hx,Complex.one_re]
      exact (hscale x (subset_closure hx)).2
    · intro x hx
      rw [hub x hx,hWb x hx]
  refine ⟨hle,?_⟩
  intro x hx y hy
  have hm : IsMinOn (fun z => W z-u z) (closure U) x := by
    intro z hz
    change W x-u x ≤ W z-u z
    rw [hWb x hx,hub x hx,sub_self]
    exact sub_nonneg.mpr (hle z hz)
  have hdu := closureJet_hasFDerivWithinAt hU hconv
    (hu.differentiableOn (by norm_num)) J (frontier_subset_closure hx)
  have hdW : HasFDerivWithinAt W (fderiv ℝ W x) (closure U) x :=
    (hW.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hh := hm.localize.hasFDerivWithinAt_nonneg (hdW.sub hdu)
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))
  have hder : fderiv ℝ W x = c • fderiv ℝ w x :=
    fderiv_const_mul (hw.contDiffAt.differentiableAt (by norm_num)) c
  rw [hder] at hh
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,sub_nonneg] using hh

end PowerConvexity
