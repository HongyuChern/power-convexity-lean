import PowerConvexity.Analysis.StrictBoundaryChords
import PowerConvexity.Calculus.DefiningFunctionInteriorBall
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! # A smooth strictly convex domain with a flat tangential second derivative

The example { z : (Re z)^4+(Im z)^2 < 1 } distinguishes strict boundary
chords from positive definiteness of the second fundamental form.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

noncomputable def flatBoundaryDefining (z : ℂ) : ℝ := z.re^4+z.im^2-1
def flatBoundaryDomain : Set ℂ := {z | flatBoundaryDefining z < 0}

theorem flatBoundaryDefining_smooth : ContDiff ℝ ∞ flatBoundaryDefining := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re^4+z.im^2-1)
  exact ((Complex.reCLM.contDiff.pow 4).add (Complex.imCLM.contDiff.pow 2)).sub contDiff_const

theorem flatBoundaryDefining_strictConvex : StrictConvexOn ℝ univ flatBoundaryDefining := by
  have h4 : StrictConvexOn ℝ univ (fun r : ℝ => r^4) :=
    (by norm_num : Even (4:ℕ)).strictConvexOn_pow (by norm_num)
  have h2 : StrictConvexOn ℝ univ (fun r : ℝ => r^2) :=
    (by norm_num : Even (2:ℕ)).strictConvexOn_pow (by norm_num)
  refine ⟨convex_univ,?_⟩
  intro x _ y _ hxy a b ha hb hab
  have h4le := h4.convexOn.2 (mem_univ x.re) (mem_univ y.re) ha.le hb.le hab
  have h2le := h2.convexOn.2 (mem_univ x.im) (mem_univ y.im) ha.le hb.le hab
  simp only [smul_eq_mul] at h4le h2le
  simp only [flatBoundaryDefining,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,smul_eq_mul]
  by_cases hre : x.re = y.re
  · have him : x.im ≠ y.im := fun h => hxy (Complex.ext hre h)
    have hh := h2.2 (mem_univ x.im) (mem_univ y.im) him ha hb hab
    simp only [smul_eq_mul] at hh
    nlinarith
  · have hh := h4.2 (mem_univ x.re) (mem_univ y.re) hre ha hb hab
    simp only [smul_eq_mul] at hh
    nlinarith

theorem flatBoundaryDomain_isOpen : IsOpen flatBoundaryDomain :=
  isOpen_lt flatBoundaryDefining_smooth.continuous continuous_const

theorem flatBoundaryDefining_nonpos_closure {z : ℂ} (hz : z ∈ closure flatBoundaryDomain) :
    flatBoundaryDefining z ≤ 0 := by
  have hc : IsClosed {z : ℂ | flatBoundaryDefining z ≤ 0} :=
    isClosed_le flatBoundaryDefining_smooth.continuous continuous_const
  have hs : flatBoundaryDomain ⊆ {z : ℂ | flatBoundaryDefining z ≤ 0} :=
    fun y hy => (show flatBoundaryDefining y < 0 from hy).le
  exact (hc.closure_subset_iff.mpr hs) hz

theorem flatBoundaryDomain_strictBoundaryChords : HasStrictBoundaryChords flatBoundaryDomain := by
  intro x hx y hy hxy a b ha hb hab
  have hh := flatBoundaryDefining_strictConvex.2 (mem_univ x) (mem_univ y) hxy ha hb hab
  have hx0 := flatBoundaryDefining_nonpos_closure hx
  have hy0 := flatBoundaryDefining_nonpos_closure hy
  have hsum : a*flatBoundaryDefining x+b*flatBoundaryDefining y ≤ 0 :=
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le hx0) (mul_nonpos_of_nonneg_of_nonpos hb.le hy0)
  exact hh.trans_le hsum

theorem flatBoundaryDomain_bounded : Bornology.IsBounded flatBoundaryDomain := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2,?_⟩
  intro z hz
  change z.re^4+z.im^2-1 < 0 at hz
  have hr2 : z.re^2 < 1 := by nlinarith [sq_nonneg (z.re^2-1),sq_nonneg z.im,sq_nonneg z.re]
  have hi2 : z.im^2 < 1 := by nlinarith [sq_nonneg (z.re^2)]
  have hn : ‖z‖^2 = z.re^2+z.im^2 := by simpa [Complex.normSq_apply,pow_two] using Complex.sq_norm z
  nlinarith [norm_nonneg z]

theorem flatBoundaryDefining_hasFDerivAt (z : ℂ) :
    HasFDerivAt flatBoundaryDefining
      ((4*z.re^3) • Complex.reCLM+(2*z.im) • Complex.imCLM) z := by
  have hh := ((Complex.reCLM.hasFDerivAt (x := z)).pow 4).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt (fun z : ℂ => z.re^4+z.im^2-1) _ z
  simpa [Pi.add_apply,smul_smul] using hh.sub_const 1

theorem flatBoundaryDefining_fderiv (z : ℂ) :
    fderiv ℝ flatBoundaryDefining z =
      (4*z.re^3) • Complex.reCLM+(2*z.im) • Complex.imCLM :=
  (flatBoundaryDefining_hasFDerivAt z).fderiv

theorem flatBoundaryDefining_realHessian (z v w : ℂ) :
    realHessian flatBoundaryDefining z v w = 12*z.re^2*v.re*w.re+2*v.im*w.im := by
  have he : fderiv ℝ flatBoundaryDefining =
      fun z => (4*z.re^3) • Complex.reCLM+(2*z.im) • Complex.imCLM :=
    funext flatBoundaryDefining_fderiv
  have h1 := (((Complex.reCLM.hasFDerivAt (x := z)).pow 3).const_mul 4).smul_const Complex.reCLM
  have h2 := ((Complex.imCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.imCLM
  have hh := h1.add h2
  change HasFDerivAt (fun z : ℂ => (4*z.re^3) • Complex.reCLM+(2*z.im) • Complex.imCLM) _ z at hh
  unfold realHessian
  rw [he,hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  norm_num <;> ring_nf <;> simp

theorem flatBoundaryDefining_zero_frontier {z : ℂ} (hz : z ∈ frontier flatBoundaryDomain) :
    flatBoundaryDefining z = 0 := by
  have hle := flatBoundaryDefining_nonpos_closure (frontier_subset_closure hz)
  have hnot : z ∉ flatBoundaryDomain := by
    rw [flatBoundaryDomain_isOpen.frontier_eq] at hz
    exact hz.2
  exact le_antisymm hle (not_lt.mp hnot)

theorem flatBoundaryDomain_smooth : HasSmoothLocalDefiningFunction flatBoundaryDomain := by
  intro z hz
  have hzero := flatBoundaryDefining_zero_frontier hz
  refine ⟨flatBoundaryDefining,flatBoundaryDefining_smooth.contDiffAt,hzero,?_,
    Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩
  intro hD
  have hR := congrArg (fun D : ℂ →L[ℝ] ℝ => D 1) hD
  have hI := congrArg (fun D : ℂ →L[ℝ] ℝ => D Complex.I) hD
  rw [flatBoundaryDefining_fderiv] at hR hI
  norm_num [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hR hI
  norm_num [flatBoundaryDefining,hR,hI] at hzero

theorem flatBoundaryDomain_I_frontier : Complex.I ∈ frontier flatBoundaryDomain := by
  have hsub : openSegment ℝ (0:ℂ) Complex.I ⊆ flatBoundaryDomain := by
    rintro z ⟨a,b,ha,hb,hab,rfl⟩
    have hh := flatBoundaryDefining_strictConvex.2 (mem_univ (0:ℂ)) (mem_univ Complex.I)
      (by exact Complex.I_ne_zero.symm) ha hb hab
    change flatBoundaryDefining (a • (0:ℂ)+b • Complex.I) < 0
    apply hh.trans
    norm_num [flatBoundaryDefining,smul_eq_mul]
    linarith
  have hc : Complex.I ∈ closure flatBoundaryDomain :=
    closure_mono hsub (segment_subset_closure_openSegment (right_mem_segment ℝ (0:ℂ) Complex.I))
  rw [flatBoundaryDomain_isOpen.frontier_eq]
  refine ⟨hc,?_⟩
  norm_num [flatBoundaryDomain,flatBoundaryDefining]

theorem flatBoundaryDomain_flat_tangent :
    (1:ℂ) ≠ 0 ∧ fderiv ℝ flatBoundaryDefining Complex.I 1 = 0 ∧
      realHessian flatBoundaryDefining Complex.I 1 1 = 0 := by
  rw [flatBoundaryDefining_fderiv,flatBoundaryDefining_realHessian]
  norm_num [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]

end PowerConvexity
