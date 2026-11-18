import PowerConvexity.Calculus.VariableDensityDirectionalHessianTwo

/-! # Uniform second-variation source bounds for the constructed density path -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem density_second_source_lower_of_bounds
    {d a b A B : ℝ} (hd : 1 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ A) :
    -(B+A^2) ≤ (a*d-b^2)/d^2 := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hd2 : 1 ≤ d^2 := by nlinarith
  have hb2 : b^2 ≤ A^2 := by nlinarith [(abs_le.mp hb).1,(abs_le.mp hb).2]
  have hquot : b^2/d^2 ≤ A^2 := (div_le_self (sq_nonneg b) hd2).trans hb2
  have haq : -B ≤ a/d := by
    apply (le_div_iff₀ hd0).mpr
    have hBd := mul_le_mul_of_nonneg_left hd hB
    have hal := (abs_le.mp ha).1
    nlinarith
  have he : (a*d-b^2)/d^2 = a/d-b^2/d^2 := by field_simp
  rw [he]
  linarith

variable [FiniteDimensional ℝ E]

theorem dirichletContinuationDensityTwo_uniform_second_source
    (a b : Fin 2 → E) {V : Set E} (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V,
      ∀ v : E, ‖v‖ = 1 →
      -C ≤ (realHessian (dirichletContinuationDensityTwo a b w s) x v v*
          dirichletContinuationDensityTwo a b w s x-
          (fderiv ℝ (dirichletContinuationDensityTwo a b w s) x v)^2)/
            (dirichletContinuationDensityTwo a b w s x)^2 := by
  let d : E → ℝ := fun x => (complexHessian a b w x).det.re
  have hd2 : ContDiff ℝ 2 d := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact Complex.reCLM.contDiff.contDiffAt.comp x
      (field_det_contDiffAt (complexHessian_contDiffAt_two hw.contDiffAt a b))
  have hDc : Continuous (fderiv ℝ d) := (hd2.fderiv_right (m := 1) (by norm_num)).continuous
  have hHc : Continuous (realHessian d) :=
    ((hd2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hD : Continuous (fun p : E × E => fderiv ℝ d p.1 p.2) :=
    (hDc.comp continuous_fst).clm_apply continuous_snd
  have hH : Continuous (fun p : E × E => realHessian d p.1 p.2 p.2) :=
    ((hHc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hprod := hK.prod (isCompact_sphere (0 : E) 1)
  obtain ⟨A,hA⟩ := hprod.exists_bound_of_continuousOn hD.continuousOn
  obtain ⟨B,hB⟩ := hprod.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max B 0+(max A 0)^2,add_nonneg (le_max_right _ _) (sq_nonneg _),?_⟩
  intro s hs x hx v hv
  have hvS : (x,v) ∈ closure V ×ˢ sphere (0 : E) 1 :=
    ⟨hx,by simpa only [mem_sphere,dist_zero_right] using hv⟩
  have hDv : |fderiv ℝ d x v| ≤ max A 0 :=
    (by simpa only [Real.norm_eq_abs] using hA (x,v) hvS : |fderiv ℝ d x v| ≤ A).trans
      (le_max_left _ _)
  have hHv : |realHessian d x v v| ≤ max B 0 :=
    (by simpa only [Real.norm_eq_abs] using hB (x,v) hvS : |realHessian d x v v| ≤ B).trans
      (le_max_left _ _)
  have hs0 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hs1 : 1-s ≤ 1 := by linarith [hs.1]
  have hdf : |fderiv ℝ (dirichletContinuationDensityTwo a b w s) x v| ≤ max A 0 := by
    change |fderiv ℝ (fun y => (1-s)*d y+s) x v| ≤ _
    rw [fderiv_add_const,fderiv_const_mul (hd2.contDiffAt.differentiableAt (by norm_num)),
      ContinuousLinearMap.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hs0]
    exact ((mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hDv))
  have hhf : |realHessian (dirichletContinuationDensityTwo a b w s) x v v| ≤ max B 0 := by
    change |realHessian (fun y => (1-s)*d y+s) x v v| ≤ _
    rw [realHessian_add_const,realHessian_const_mul]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hs0]
    exact ((mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hHv))
  exact density_second_source_lower_of_bounds
    (dirichletContinuationDensityTwo_bounds a b hs (hd x hx)).1
    (le_max_right _ _) (le_max_right _ _) hhf hdf

end PowerConvexity
