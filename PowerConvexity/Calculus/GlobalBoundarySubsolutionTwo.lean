import PowerConvexity.Analysis.CompactPositiveScaling
import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # A single global C4 function with determinant greater than one near the boundary

The determinant and strict psh assertions hold on a genuine open neighborhood
of the whole compact boundary. They are not asserted on the remaining interior.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem global_C4_boundary_subsolution_of_strictPsh_neighborhood_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (frontier U))
    {rho : E → ℝ} (hrho : ContDiff ℝ 4 rho)
    (hb : ∀ x ∈ frontier U, rho x = 0 ∧ fderiv ℝ rho x ≠ 0)
    {W : Set E} (hWo : IsOpen W) (hKW : frontier U ⊆ W)
    (hW : ∀ z ∈ W, (z ∈ U ↔ rho z < 0) ∧ (complexHessian a b rho z).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧
      (∀ x ∈ frontier U, w x = 0 ∧ fderiv ℝ w x ≠ 0) ∧
      ∃ V : Set E, IsOpen V ∧ frontier U ⊆ V ∧
        ∀ z ∈ V, (z ∈ U ↔ w z < 0) ∧
          (complexHessian a b w z).PosDef ∧ (1 : ℂ) < (complexHessian a b w z).det := by
  have hrho2 : ContDiff ℝ 2 rho := hrho.of_le (by norm_num)
  let d : E → ℝ := fun z => (complexHessian a b rho z).det.re
  have hdc : Continuous d := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (complexHessian_continuousAt_of_C2 a b hrho2.contDiffAt)
  obtain ⟨c,hc1,hcK⟩ := exists_uniform_square_scaling_gt_one hK hdc
    (fun x hx => (Complex.pos_iff.mp ((hW x (hKW hx)).2.det_pos)).1)
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let w : E → ℝ := fun z => c*rho z
  have hw : ContDiff ℝ 4 w := contDiff_const.mul hrho
  let V : Set E := W ∩ {z | 1 < c^2*d z}
  have hVo : IsOpen V := hWo.inter (isOpen_lt continuous_const (continuous_const.mul hdc))
  have hKV : frontier U ⊆ V := fun x hx => ⟨hKW hx,hcK x hx⟩
  refine ⟨w,hw,?_,V,hVo,hKV,?_⟩
  · intro x hx
    refine ⟨by simp only [w,(hb x hx).1,mul_zero],?_⟩
    change fderiv ℝ (fun z => c*rho z) x ≠ 0
    rw [fderiv_const_mul (hrho2.contDiffAt.differentiableAt (by norm_num))]
    exact smul_ne_zero hc.ne' (hb x hx).2
  · intro z hz
    have hscale := complexHessian_const_mul_at hrho2.contDiffAt c a b (x := z)
    have hp : (complexHessian a b w z).PosDef := by
      change (complexHessian a b (fun y => c*rho y) z).PosDef
      rw [hscale]
      exact (hW z hz.1).2.smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    refine ⟨?_,hp,?_⟩
    · rw [(hW z hz.1).1]
      change rho z < 0 ↔ c*rho z < 0
      constructor
      · exact mul_neg_of_pos_of_neg hc
      · intro hh
        by_contra! hnn
        exact (not_lt_of_ge (mul_nonneg hc.le hnn)) hh
    · have he : (complexHessian a b w z).det.re = c^2*d z := by
        change (complexHessian a b (fun y => c*rho y) z).det.re = _
        rw [hscale,Matrix.det_smul]
        simp [d,Complex.mul_re,Complex.mul_im,pow_two]
      apply Complex.lt_def.mpr
      exact ⟨by simpa only [Complex.one_re,he] using (show 1 < c^2*d z from hz.2),
        by simpa only [Complex.one_im] using (Complex.pos_iff.mp hp.det_pos).2⟩

end PowerConvexity
