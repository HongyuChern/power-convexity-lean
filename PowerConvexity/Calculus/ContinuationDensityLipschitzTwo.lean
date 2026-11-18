import PowerConvexity.Calculus.DirichletContinuationDensityTwo
import Mathlib.Analysis.Calculus.MeanValue

/-! # A uniform actual Lipschitz bound for the fixed continuation density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem dirichletContinuationDensityTwo_uniform_lipschitz
    (a b : Fin 2 → E) {U : Set E} (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        |dirichletContinuationDensityTwo a b w s x-
          dirichletContinuationDensityTwo a b w s y| ≤ L*‖x-y‖ := by
  let d : E → ℝ := fun x => (complexHessian a b w x).det.re
  have hd2 : ContDiff ℝ 2 d := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact Complex.reCLM.contDiff.contDiffAt.comp x
      (field_det_contDiffAt (complexHessian_contDiffAt_two hw.contDiffAt a b))
  have hDc : Continuous (fderiv ℝ d) := (hd2.fderiv_right (m := 1) (by norm_num)).continuous
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hDc.continuousOn
  let L : ℝ := max A 0
  have hL : 0 ≤ L := le_max_right _ _
  have hdLip (x : E) (hx : x ∈ closure U) (y : E) (hy : y ∈ closure U) :
      |d x-d y| ≤ L*‖x-y‖ := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ closure U) => hd2.contDiffAt.differentiableAt (by norm_num))
      (fun z hz => (hA z hz).trans (le_max_left _ _)) hconv.closure hy hx
  refine ⟨L,hL,?_⟩
  intro s hs x hx y hy
  have he : dirichletContinuationDensityTwo a b w s x-
      dirichletContinuationDensityTwo a b w s y = (1-s)*(d x-d y) := by
    dsimp only [dirichletContinuationDensityTwo,d]
    ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hfac : 1-s ≤ 1 := by linarith [hs.1]
  exact (mul_le_mul_of_nonneg_right hfac (abs_nonneg _)).trans
    (by simpa only [one_mul] using hdLip x hx y hy)

end PowerConvexity
