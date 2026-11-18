import PowerConvexity.Calculus.GlobalBoundarySubsolutionTwo
import CHS.Calculus.ClosureRegularity

/-! # A genuine global strict CMA subsolution with actual closure jets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem global_C4_strict_subsolution_of_strictPsh_closure_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (closure U))
    {rho : E → ℝ} (hrho : ContDiff ℝ 4 rho)
    (hb : ∀ x ∈ frontier U, rho x = 0 ∧ fderiv ℝ rho x ≠ 0)
    (hpos : ∀ x ∈ closure U, (complexHessian a b rho x).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧ Nonempty (ClosureC2Jet w U) ∧
      (∀ x ∈ frontier U, w x = 0 ∧ fderiv ℝ w x ≠ 0) ∧
      ∀ x ∈ closure U, (complexHessian a b w x).PosDef ∧
        (1 : ℂ) < (complexHessian a b w x).det := by
  have hrho2 : ContDiff ℝ 2 rho := hrho.of_le (by norm_num)
  let d : E → ℝ := fun x => (complexHessian a b rho x).det.re
  have hdc : Continuous d := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (complexHessian_continuousAt_of_C2 a b hrho2.contDiffAt)
  obtain ⟨c,hc1,hcK⟩ := exists_uniform_square_scaling_gt_one hK hdc
    (fun x hx => (Complex.pos_iff.mp (hpos x hx).det_pos).1)
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let w : E → ℝ := fun x => c*rho x
  have hw : ContDiff ℝ 4 w := contDiff_const.mul hrho
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hJ : Nonempty (ClosureC2Jet w U) :=
    (c2OnClosure_of_neighborhood isOpen_univ (subset_univ _) hw2.contDiffOn).2
  refine ⟨w,hw,hJ,?_,?_⟩
  · intro x hx
    refine ⟨by simp only [w,(hb x hx).1,mul_zero],?_⟩
    change fderiv ℝ (fun y => c*rho y) x ≠ 0
    rw [fderiv_const_mul (hrho2.contDiffAt.differentiableAt (by norm_num))]
    exact smul_ne_zero hc.ne' (hb x hx).2
  · intro x hx
    have hscale := complexHessian_const_mul_at hrho2.contDiffAt c a b (x := x)
    have hp : (complexHessian a b w x).PosDef := by
      change (complexHessian a b (fun y => c*rho y) x).PosDef
      rw [hscale]
      exact (hpos x hx).smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    refine ⟨hp,?_⟩
    have he : (complexHessian a b w x).det.re = c^2*d x := by
      change (complexHessian a b (fun y => c*rho y) x).det.re = _
      rw [hscale,Matrix.det_smul]
      simp [d,Complex.mul_re,Complex.mul_im,pow_two]
    apply Complex.lt_def.mpr
    exact ⟨by simpa only [Complex.one_re,he] using hcK x hx,
      by simpa only [Complex.one_im] using (Complex.pos_iff.mp hp.det_pos).2⟩

end PowerConvexity
