import PowerConvexity.Calculus.RealHessianQuotient
import PowerConvexity.Algebra.HermitianQuotientCoordinatesTwo
import Mathlib.Analysis.Matrix.Normed

/-! # Actual operator-norm jet bounds after constant matrix sandwiches -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity

noncomputable def matrixEntryRealCLM (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (Fin 2 → ℂ))

noncomputable def sandwichEntryCLM (Q R : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  ∑ p, ∑ q, (Q i p*R q j) • matrixEntryRealCLM p q

noncomputable def sandwichReEntryCLM (Q R : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (sandwichEntryCLM Q R i j)
noncomputable def sandwichImEntryCLM (Q R : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp (sandwichEntryCLM Q R i j)

theorem sandwichEntryCLM_apply (Q R M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    sandwichEntryCLM Q R i j M = (Q*M*R) i j := by
  simp only [sandwichEntryCLM,matrixEntryRealCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Matrix.mul_apply,
    Fin.sum_univ_two]
  change (Q i 0*R 0 j)*M 0 0+(Q i 0*R 1 j)*M 0 1+
    ((Q i 1*R 0 j)*M 1 0+(Q i 1*R 1 j)*M 1 1) = _
  ring

theorem sandwichEntryCLM_norm_bound {Q R : Matrix (Fin 2) (Fin 2) ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hQ : ∀ i j, ‖Q i j‖ ≤ K) (hR : ∀ i j, ‖R i j‖ ≤ K) (i j : Fin 2) :
    ‖sandwichEntryCLM Q R i j‖ ≤ 4*K^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro M
  have hentry (p q : Fin 2) : ‖M p q‖ ≤ ‖M‖ :=
    (norm_le_pi_norm (M p) q).trans (norm_le_pi_norm M p)
  have hb (p q : Fin 2) : ‖Q i p*R q j*M p q‖ ≤ K*K*‖M‖ := by
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul (hQ i p) (hR q j) (norm_nonneg _) hK)
      (hentry p q) (norm_nonneg _) (mul_nonneg hK hK)
  change ‖∑ p,∑ q,(Q i p*R q j)*M p q‖ ≤ _
  calc
    _ ≤ ∑ p,‖∑ q,(Q i p*R q j)*M p q‖ := norm_sum_le _ _
    _ ≤ ∑ p,∑ q,‖(Q i p*R q j)*M p q‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_sum_le _ _
    _ ≤ ∑ _p : Fin 2,∑ _q : Fin 2,K*K*‖M‖ := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      exact hb p q
    _ = _ := by simp [Fin.sum_univ_two]; ring

theorem sandwichReImEntryCLM_norm_bound {Q R : Matrix (Fin 2) (Fin 2) ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hQ : ∀ i j, ‖Q i j‖ ≤ K) (hR : ∀ i j, ‖R i j‖ ≤ K) (i j : Fin 2) :
    ‖sandwichReEntryCLM Q R i j‖ ≤ 4*K^2 ∧ ‖sandwichImEntryCLM Q R i j‖ ≤ 4*K^2 := by
  have hb := sandwichEntryCLM_norm_bound hK hQ hR i j
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro M
    calc
      _ ≤ ‖sandwichEntryCLM Q R i j M‖ := Complex.abs_re_le_norm _
      _ ≤ ‖sandwichEntryCLM Q R i j‖*‖M‖ := (sandwichEntryCLM Q R i j).le_opNorm M
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (norm_nonneg M)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro M
    calc
      _ ≤ ‖sandwichEntryCLM Q R i j M‖ := Complex.abs_im_le_norm _
      _ ≤ ‖sandwichEntryCLM Q R i j‖*‖M‖ := (sandwichEntryCLM Q R i j).le_opNorm M
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (norm_nonneg M)

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
open CHS.Calculus

theorem fderiv_linear_projection_norm_bound {F : E → V} {x : E}
    (hF : DifferentiableAt ℝ F x) (c : V →L[ℝ] ℝ) :
    ‖fderiv ℝ (fun y => c (F y)) x‖ ≤ ‖c‖*‖fderiv ℝ F x‖ := by
  have heq : fderiv ℝ (fun y => c (F y)) x = c.comp (fderiv ℝ F x) :=
    (c.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  rw [heq]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem realHessian_linear_projection_eq {F : E → V} {x : E}
    (hF : ContDiffAt ℝ 2 F x) (c : V →L[ℝ] ℝ) :
    realHessian (fun y => c (F y)) x =
      (ContinuousLinearMap.compL ℝ E V ℝ c).comp (fderiv ℝ (fderiv ℝ F) x) := by
  have heq : fderiv ℝ (fun y => c (F y)) =ᶠ[𝓝 x] fun y => c.comp (fderiv ℝ F y) := by
    filter_upwards [hF.eventually (by simp)] with y hy
    exact (c.hasFDerivAt.comp y (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold realHessian
  rw [heq.fderiv_eq]
  exact ((ContinuousLinearMap.compL ℝ E V ℝ c).hasFDerivAt.comp x hDF.hasFDerivAt).fderiv

theorem realHessian_linear_projection_norm_bound {F : E → V} {x : E}
    (hF : ContDiffAt ℝ 2 F x) (c : V →L[ℝ] ℝ) :
    ‖realHessian (fun y => c (F y)) x‖ ≤ ‖c‖*‖fderiv ℝ (fderiv ℝ F) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [realHessian_linear_projection_eq hF c]
  change ‖c (fderiv ℝ (fderiv ℝ F) x v w)‖ ≤ _
  calc
    _ ≤ ‖c‖*‖fderiv ℝ (fderiv ℝ F) x v w‖ := c.le_opNorm _
    _ ≤ ‖c‖*(‖fderiv ℝ (fderiv ℝ F) x v‖*‖w‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ F) x v).le_opNorm w) (norm_nonneg c)
    _ ≤ ‖c‖*((‖fderiv ℝ (fderiv ℝ F) x‖*‖v‖)*‖w‖) := by
      gcongr
      exact (fderiv ℝ (fderiv ℝ F) x).le_opNorm v
    _ = _ := by ring

theorem exists_eventually_first_second_fderiv_norm_bound {F : E → V} {x : E}
    (hF : ContDiffAt ℝ 2 F x) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ F y‖ ≤ K ∧ ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ K := by
  have hD := hF.fderiv_right (m := 1) (by norm_num)
  have hDD := hD.fderiv_right (m := 0) (by norm_num)
  let K := max 1 (max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖)+1
  have hK : 1 ≤ K := by dsimp only [K]; linarith [le_max_left (1:ℝ) (max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖)]
  have h1 : ‖fderiv ℝ F x‖ < K := by
    have hh := (le_max_left ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖).trans
      (le_max_right (1:ℝ) (max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖))
    dsimp only [K]
    linarith
  have h2 : ‖fderiv ℝ (fderiv ℝ F) x‖ < K := by
    have hh := (le_max_right ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖).trans
      (le_max_right (1:ℝ) (max ‖fderiv ℝ F x‖ ‖fderiv ℝ (fderiv ℝ F) x‖))
    dsimp only [K]
    linarith
  have hc1 : ContinuousAt (fun y => ‖fderiv ℝ F y‖) x := hD.continuousAt.norm
  have hc2 : ContinuousAt (fun y => ‖fderiv ℝ (fderiv ℝ F) y‖) x := hDD.continuousAt.norm
  refine ⟨K,hK,?_⟩
  filter_upwards [hc1.eventually (gt_mem_nhds h1),hc2.eventually (gt_mem_nhds h2)] with y hy1 hy2
  exact ⟨hy1.le,hy2.le⟩

end PowerConvexity
