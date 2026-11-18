import PowerConvexity.Calculus.LocalStrictPshMinkowskiTwo
import CHS.Calculus.ClosureJets

/-! # Local zero-boundary strict subsolutions with determinant greater than one

The construction is on a genuine neighborhood of each actual boundary point.
It does not assert that these local functions have been patched globally.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexHessian_continuousAt_of_C2 {ι : Type*} (a b : ι → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (fun y => complexHessian a b f y) x := by
  have hH : ContinuousAt (realHessian f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  apply ((continuous_jetComplexHessian a b).continuousAt.comp hH).congr
  filter_upwards [hf.eventually (by simp)] with y hy
  funext i j
  exact (complexHessian_real_entry hy a b i j).symm

theorem exists_positive_scaling_det_gt_one_two (a b : Fin 2 → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hp : ∀ᶠ y in 𝓝 x, (complexHessian a b f y).PosDef) :
    ∃ c > 0, ∀ᶠ y in 𝓝 x,
      (complexHessian a b (fun z => c*f z) y).PosDef ∧
      (1 : ℂ) < (complexHessian a b (fun z => c*f z) y).det := by
  have hp0 := hp.self_of_nhds
  let d := (complexHessian a b f x).det.re/2
  have hd : 0 < d := half_pos (Complex.pos_iff.mp hp0.det_pos).1
  let c := 1/d+1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : 1 < c := by dsimp only [c]; linarith [div_pos (by norm_num : (0 : ℝ) < 1) hd]
  have hcd : c*d = 1+d := by dsimp only [c]; rw [add_mul,one_mul,div_mul_cancel₀ _ hd.ne']
  have hcd1 : 1 < c*d := by rw [hcd]; linarith
  have hc2d : 1 < c^2*d := by
    have hh := mul_le_mul_of_nonneg_right hc1.le (mul_nonneg hc.le hd.le)
    nlinarith
  have hdetc : ContinuousAt (fun y => (complexHessian a b f y).det.re) x :=
    ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (complexHessian_continuousAt_of_C2 a b hf)
  have hsmall : d < (complexHessian a b f x).det.re := half_lt_self (Complex.pos_iff.mp hp0.det_pos).1
  refine ⟨c,hc,?_⟩
  filter_upwards [hp,hf.eventually (by simp),hdetc.tendsto.eventually (lt_mem_nhds hsmall)]
    with y hpy hfy hdy
  have hscale := complexHessian_const_mul_at hfy c a b
  have hpos : (complexHessian a b (fun z => c*f z) y).PosDef := by
    rw [hscale]
    exact hpy.smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  refine ⟨hpos,?_⟩
  have hreal : (complexHessian a b (fun z => c*f z) y).det.re =
      c^2*(complexHessian a b f y).det.re := by
    rw [hscale,Matrix.det_smul]
    simp [Complex.mul_re,Complex.mul_im,pow_two]
  apply Complex.lt_def.mpr
  constructor
  · simp only [Complex.one_re,hreal]
    have hh := mul_le_mul_of_nonneg_left hdy.le (sq_nonneg c)
    linarith
  · simpa only [Complex.one_im] using (Complex.pos_iff.mp hpos.det_pos).2

theorem exists_local_zero_boundary_subsolution_two
    (a b : Fin 2 → E) {U : Set E} (hU : IsOpen U) {x : E}
    {rho : E → ℝ} (hrho : ContDiffAt ℝ ∞ rho x) (hrx : rho x = 0)
    (hDrho : fderiv ℝ rho x ≠ 0)
    (hrdef : ∀ᶠ y in 𝓝 x, y ∈ U ↔ rho y < 0)
    (hrpos : ∀ᶠ y in 𝓝 x, (complexHessian a b rho y).PosDef) :
    ∃ w : E → ℝ, ContDiffAt ℝ ∞ w x ∧ w x = 0 ∧ fderiv ℝ w x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, (y ∈ U ↔ w y < 0) ∧ ContDiffAt ℝ 4 w y ∧
        (y ∈ frontier U → w y = 0) ∧
        (complexHessian a b w y).PosDef ∧ (1 : ℂ) < (complexHessian a b w y).det) := by
  obtain ⟨c,hc,hscaled⟩ := exists_positive_scaling_det_gt_one_two a b
    ((contDiffAt_infty.mp hrho) 2) hrpos
  let w : E → ℝ := fun y => c*rho y
  have hw : ContDiffAt ℝ ∞ w x := contDiffAt_const.mul hrho
  have hwD : fderiv ℝ w x ≠ 0 := by
    rw [show w = fun y => c*rho y from rfl,fderiv_const_mul (hrho.differentiableAt (by simp))]
    exact smul_ne_zero hc.ne' hDrho
  have hwdef : ∀ᶠ y in 𝓝 x, y ∈ U ↔ w y < 0 := by
    filter_upwards [hrdef] with y hy
    rw [hy]
    change rho y < 0 ↔ c*rho y < 0
    constructor
    · exact mul_neg_of_pos_of_neg hc
    · intro hh
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hc.le hnn)) hh
  have hw4 : ContDiffAt ℝ 4 w x := (contDiffAt_infty.mp hw) 4
  refine ⟨w,hw,by simp [w,hrx],hwD,?_⟩
  filter_upwards [hwdef,hwdef.eventually_nhds,hw4.eventually (by simp),hscaled]
    with y hydef hydefn hyreg hyp
  refine ⟨hydef,hyreg,?_,hyp.1,hyp.2⟩
  intro hy
  have hyn : y ∉ U := by rw [hU.frontier_eq] at hy; exact hy.2
  apply le_antisymm
  · by_contra! hpos
    have he : ∀ᶠ z in 𝓝 y, 0 < w z := hyreg.continuousAt.tendsto.eventually (lt_mem_nhds hpos)
    obtain ⟨z,hz,hpz,hdz⟩ := ((mem_closure_iff_frequently.mp (frontier_subset_closure hy)).and_eventually
      (he.and hydefn)).exists
    have hn := hdz.mp hz
    linarith
  · by_contra! hneg
    exact hyn (hydefn.self_of_nhds.mpr hneg)

end PowerConvexity
