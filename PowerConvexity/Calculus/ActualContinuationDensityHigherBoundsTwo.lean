import PowerConvexity.Calculus.DirichletContinuationDensityC4Two
import PowerConvexity.Calculus.ActualHigherDerivativeIdentitiesTwo

/-! # Uniform first, second and third derivatives of the actual density path -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology
local instance acdhNormSMulSecond : NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toNormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance atjInstance4
local instance acdhNormSMulThird : NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toNormSMulClass ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance ahdTripleNormedSpace

theorem actual_affine_density_uniform_third_jets
    {K : Set E} (hK : IsCompact K) {d : E → ℝ} (hd : ContDiff ℝ 4 d) :
    ∃ D ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖fderiv ℝ (fun y => (1-s)*d y+s) x‖ ≤ D ∧
      ‖realHessian (fun y => (1-s)*d y+s) x‖ ≤ D ∧
      ‖fderiv ℝ (realHessian (fun y => (1-s)*d y+s)) x‖ ≤ D := by
  have hd1 : ContDiff ℝ 3 (fderiv ℝ d) := hd.fderiv_right (m := 3) (by norm_num)
  have hd2 : ContDiff ℝ 2 (realHessian d) := hd1.fderiv_right (m := 2) (by norm_num)
  have hd3 : ContDiff ℝ 1 (fderiv ℝ (realHessian d)) := hd2.fderiv_right (m := 1) (by norm_num)
  obtain ⟨A₁,hA₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ d) hd1.continuous.continuousOn
  obtain ⟨A₂,hA₂⟩ := hK.exists_bound_of_continuousOn (f := realHessian d) hd2.continuous.continuousOn
  obtain ⟨A₃,hA₃⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (realHessian d)) hd3.continuous.continuousOn
  let D := max 0 (max A₁ (max A₂ A₃))
  have hD : 0 ≤ D := le_max_left _ _
  have h1 : A₁ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : A₂ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h3 : A₃ ≤ D := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨D,hD,?_⟩
  intro s hs x hx
  have hs0 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hs1 : 1-s ≤ 1 := by linarith [hs.1]
  have hscale (a : ℝ) (ha : 0 ≤ a) (haD : a ≤ D) : (1-s)*a ≤ D :=
    (mul_le_mul_of_nonneg_right hs1 ha).trans (by simpa only [one_mul] using haD)
  have hH : realHessian (fun y => (1-s)*d y+s) = fun y => (1-s) • realHessian d y := by
    funext y
    rw [realHessian_add_const,realHessian_const_mul]
  refine ⟨?_,?_,?_⟩
  · rw [fderiv_add_const,fderiv_const_mul (hd.contDiffAt.differentiableAt (by norm_num)),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hs0]
    exact hscale _ (norm_nonneg (fderiv ℝ d x)) ((hA₁ x hx).trans h1)
  · rw [hH,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs0]
    exact hscale _ (norm_nonneg (realHessian d x)) ((hA₂ x hx).trans h2)
  · rw [hH,fderiv_fun_const_smul (hd2.contDiffAt.differentiableAt (by norm_num)),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hs0]
    exact hscale _ (norm_nonneg (fderiv ℝ (realHessian d) x)) ((hA₃ x hx).trans h3)

end PowerConvexity

namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_continuation_density_uniform_third_jets_two
    (a b : Fin 2 → E) {U : Set E} (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) :
    ∃ D ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure U,
      ‖fderiv ℝ (dirichletContinuationDensityTwo a b w s) x‖ ≤ D ∧
      ‖realHessian (dirichletContinuationDensityTwo a b w s) x‖ ≤ D ∧
      ‖fderiv ℝ (realHessian (dirichletContinuationDensityTwo a b w s)) x‖ ≤ D := by
  have hd : ContDiff ℝ 4 (fun x => (complexHessian a b w x).det.re) := by
    have hh := dirichletContinuationDensityTwo_contDiff_C4 a b hw 0
    have he : dirichletContinuationDensityTwo a b w 0 = fun x => (complexHessian a b w x).det.re :=
      funext (dirichletContinuationDensityTwo_zero a b w)
    rwa [he] at hh
  exact actual_affine_density_uniform_third_jets hK hd

end PowerConvexity
