import PowerConvexity.Analysis.MatrixHessianContraction

/-! # Local uniform ellipticity from continuous positive matrix coefficients -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators Topology ContDiff

namespace PowerConvexity
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem matrixHessianContraction_rankOne_continuousOn (e : κ → E)
    {C : E → Matrix κ κ ℝ} {K : Set E}
    (hC : ∀ i j, ContinuousOn (fun x => C x i j) K) :
    ContinuousOn (fun p : E × E => matrixHessianContraction e (C p.1)
      (realRankOneForm p.2)) (K ×ˢ univ) := by
  simp only [matrixHessianContraction, LinearMap.coe_mk, AddHom.coe_mk,
    realRankOneForm, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_apply, smul_eq_mul]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact ((hC i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)).mul
    (((continuous_snd.inner continuous_const).mul
      (continuous_snd.inner continuous_const)).continuousOn)

theorem matrixHessianContraction_trace_continuousOn (e : κ → E)
    {C : E → Matrix κ κ ℝ} {K : Set E}
    (hC : ∀ i j, ContinuousOn (fun x => C x i j) K) :
    ContinuousOn (fun x => matrixHessianContraction e (C x) (realInnerForm (E := E))) K := by
  simp only [matrixHessianContraction, LinearMap.coe_mk, AddHom.coe_mk]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (hC i j).mul continuousOn_const

variable [ProperSpace E] [Nontrivial E]

theorem compact_matrixHessianContraction_bounds (e : Module.Basis κ ℝ E)
    {C : E → Matrix κ κ ℝ} {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hC : ∀ i j, ContinuousOn (fun x => C x i j) K)
    (hpos : ∀ x ∈ K, (C x).PosDef) :
    ∃ ell Λ : ℝ, 0 < ell ∧ 0 ≤ Λ ∧
      (∀ x ∈ K, ∀ v : E,
        ell * ‖v‖^2 ≤ matrixHessianContraction e (C x) (realRankOneForm v)) ∧
      (∀ x ∈ K, matrixHessianContraction e (C x) (realInnerForm (E := E)) ≤ Λ) := by
  let S : Set E := sphere 0 1
  have hS : S.Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_⟩
    simp [S, mem_sphere, dist_zero_right, norm_smul, hn.ne']
  let q : E × E → ℝ := fun p => matrixHessianContraction e (C p.1) (realRankOneForm p.2)
  have hq : ContinuousOn q (K ×ˢ S) :=
    (matrixHessianContraction_rankOne_continuousOn e hC).mono (prod_mono_right (subset_univ S))
  obtain ⟨p, hp, hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn
    (hne.prod hS) hq
  have hpNorm : ‖p.2‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using hp.2
  have hpNe : p.2 ≠ 0 := by intro hz; rw [hz, norm_zero] at hpNorm; norm_num at hpNorm
  have hell : 0 < q p := matrixHessianContraction_rankOne_pos e (hpos p.1 hp.1) hpNe
  have hbound (x : E) (hx : x ∈ K) (v : E) :
      q p * ‖v‖^2 ≤ matrixHessianContraction e (C x) (realRankOneForm v) := by
    by_cases hv : v = 0
    · simp [hv, realRankOneForm, matrixHessianContraction]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ S := by simp [S, w, mem_sphere, dist_zero_right, norm_smul, hn.ne']
    have hminw : q p ≤ matrixHessianContraction e (C x) (realRankOneForm w) :=
      hmin (show (x,w) ∈ K ×ˢ S from ⟨hx, hw⟩)
    have hvw : ‖v‖ • w = v := by simp [w, smul_smul, hn.ne']
    calc
      q p * ‖v‖^2 ≤ ‖v‖^2 * matrixHessianContraction e (C x) (realRankOneForm w) := by
        nlinarith [mul_le_mul_of_nonneg_right hminw (sq_nonneg ‖v‖)]
      _ = matrixHessianContraction e (C x) (realRankOneForm (‖v‖ • w)) := by
        rw [realRankOneForm_smul ‖v‖ w, map_smul, smul_eq_mul]
      _ = _ := by rw [hvw]
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
    (matrixHessianContraction_trace_continuousOn e hC)
  refine ⟨q p, max 0 (matrixHessianContraction e (C z) (realInnerForm (E := E))),
    hell, le_max_left _ _, hbound, ?_⟩
  intro x hx
  exact (hmax hx).trans (le_max_right _ _)

/-- Only a neighborhood of the contact point needs a gradient coefficient.
The matrix ellipticity constants are derived here from continuity and positivity. -/
theorem continuous_matrix_gradient_local_zero (e : Module.Basis κ ℝ E)
    {U : Set E} (hU : IsOpen U) {C : E → Matrix κ κ ℝ}
    (hC : ∀ i j, ContinuousOn (fun y => C y i j) U)
    (hpos : ∀ y ∈ U, (C y).PosDef) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    {x : E} (hx : x ∈ U) (hx0 : f x = 0)
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      matrixHessianContraction e (C y) (CHS.Calculus.realHessian f y) ≤
        c * (f y + ‖fderiv ℝ f y‖)) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  obtain ⟨c, hc, hest⟩ := hest
  have hn : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      matrixHessianContraction e (C y) (CHS.Calculus.realHessian f y) ≤
        c * (f y + ‖fderiv ℝ f y‖) := Filter.Eventually.and (hU.mem_nhds hx) hest
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hr : 0 < δ/2 := by positivity
  have hclosed : closedBall x (δ/2) ⊆ ball x δ :=
    closedBall_subset_ball (by linarith)
  have hKU : closedBall x (δ/2) ⊆ U := fun y hy => (hball (hclosed hy)).1
  obtain ⟨ell, Λ, hell, hΛ, hlow, htrace⟩ := compact_matrixHessianContraction_bounds e
    (isCompact_closedBall x (δ/2)) ⟨x, mem_closedBall_self hr.le⟩
    (fun i j => (hC i j).mono hKU) (fun y hy => hpos y (hKU hy))
  have hzero := zero_propagation_gradient_on_ball (w := f) (x := x) hr hell hΛ hc
    (fun y hy => hf.contDiffAt (hU.mem_nhds (hKU (ball_subset_closedBall hy))))
    (fun y hy => hnonneg y (hKU (ball_subset_closedBall hy))) hx0
    (fun y => matrixHessianContraction e (C y))
    (fun y hy => matrixHessianContraction_positive e
      (hpos y (hKU (ball_subset_closedBall hy))).posSemidef)
    (fun y hy => hlow y (ball_subset_closedBall hy))
    (fun y hy => htrace y (ball_subset_closedBall hy))
    (fun y hy => (hball (hclosed (ball_subset_closedBall hy))).2)
  exact Filter.Eventually.mono (ball_mem_nhds x (by positivity : 0 < (δ/2)/4)) hzero

theorem continuous_matrix_strong_minimum_positive (e : Module.Basis κ ℝ E)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {C : E → Matrix κ κ ℝ}
    (hC : ∀ i j, ContinuousOn (fun y => C y i j) U)
    (hpos : ∀ y ∈ U, (C y).PosDef) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    (hest : ∀ x ∈ U, f x = 0 → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      matrixHessianContraction e (C y) (CHS.Calculus.realHessian f y) ≤
        c * (f y + ‖fderiv ℝ f y‖))
    (hanchor : ∃ x ∈ U, 0 < f x) : ∀ x ∈ U, 0 < f x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn hf.continuousOn hnonneg
    (fun x hx hx0 => continuous_matrix_gradient_local_zero e hU hC hpos hf hnonneg hx hx0
      (hest x hx hx0)) hanchor

end PowerConvexity
