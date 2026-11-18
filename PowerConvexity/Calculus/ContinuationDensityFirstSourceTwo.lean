import PowerConvexity.Calculus.VariableDensityGradientBoundaryMaximumTwo

/-! # A uniform actual first-variation source for the fixed density path -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem dirichletContinuationDensityTwo_uniform_first_source
    (a b : Fin 2 → E) {V : Set E} (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V, ∀ v : E,
      |fderiv ℝ (dirichletContinuationDensityTwo a b w s) x v /
        dirichletContinuationDensityTwo a b w s x| ≤ C*‖v‖ := by
  let d : E → ℝ := fun x => (complexHessian a b w x).det.re
  have hd2 : ContDiff ℝ 2 d := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact Complex.reCLM.contDiff.contDiffAt.comp x
      (field_det_contDiffAt (complexHessian_contDiffAt_two hw.contDiffAt a b))
  have hDc : Continuous (fderiv ℝ d) := (hd2.fderiv_right (m := 1) (by norm_num)).continuous
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hDc.continuousOn
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro s hs x hx v
  have hDv : |fderiv ℝ d x v| ≤ max A 0*‖v‖ := by
    have he := (fderiv ℝ d x).le_opNorm v
    rw [Real.norm_eq_abs] at he
    exact he.trans (mul_le_mul_of_nonneg_right ((hA x hx).trans (le_max_left _ _)) (norm_nonneg v))
  have hs0 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hs1 : 1-s ≤ 1 := by linarith [hs.1]
  have hdf : |fderiv ℝ (dirichletContinuationDensityTwo a b w s) x v| ≤ max A 0*‖v‖ := by
    change |fderiv ℝ (fun y => (1-s)*d y+s) x v| ≤ _
    rw [fderiv_add_const,fderiv_const_mul (hd2.contDiffAt.differentiableAt (by norm_num)),
      smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hs0]
    exact ((mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hDv))
  have hlow := (dirichletContinuationDensityTwo_bounds a b hs (hd x hx)).1
  rw [abs_div,abs_of_pos (lt_of_lt_of_le zero_lt_one hlow)]
  exact (div_le_self (abs_nonneg _) hlow).trans hdf

end PowerConvexity
