import PowerConvexity.Analysis.ActualFlatPointwiseRemainderFour

/-! # The actual boundary first derivative from the proved quadratic expansion -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory Asymptotics
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_remainder_hasFDerivWithinAt_four {N : E} {u p : E → ℝ}
    (hp : IsQuadraticPolynomial p) {R M beta : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hbeta : 0 ≤ beta)
    (herr : ∀ x : E, 0 ≤ inner ℝ N x → ‖x‖ < R/2 →
      |u x-p x| ≤ M*‖x‖^2*‖x‖^beta) :
    HasFDerivWithinAt u (fderiv ℝ p 0) {x : E | 0 ≤ inner ℝ N x} 0 := by
  let S := {x : E | 0 ≤ inner ℝ N x}
  have hO : (fun x => u x-p x) =O[𝓝[S] (0 : E)] (fun x => ‖x-(0 : E)‖^2) := by
    apply Asymptotics.IsBigO.of_bound M
    have he : ∀ᶠ x : E in 𝓝 (0 : E), ‖x‖ < min (R/2) 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) (lt_min (half_pos hR) zero_lt_one)] with x hx
      simpa only [mem_ball,dist_zero_right] using hx
    filter_upwards [self_mem_nhdsWithin,he.filter_mono nhdsWithin_le_nhds] with x hx hnorm
    have hxR : ‖x‖ < R/2 := hnorm.trans_le (min_le_left _ _)
    have hx1 : ‖x‖ ≤ 1 := hnorm.le.trans (min_le_right _ _)
    have hxpow : ‖x‖^beta ≤ 1 := Real.rpow_le_one (norm_nonneg x) hx1 hbeta
    have hh := (herr x hx hxR).trans (mul_le_mul_of_nonneg_left hxpow (by positivity : 0 ≤ M*‖x‖^2))
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg (sq_nonneg ‖x‖),mul_one] using hh
  have hz : HasFDerivWithinAt (fun x => u x-p x) (0 : E →L[ℝ] ℝ) S 0 :=
    hO.hasFDerivWithinAt (by simp only [S,mem_setOf_eq,inner_zero_right,le_refl])
      (by norm_num : 1 < (2 : ℕ))
  have hpD : HasFDerivAt p (fderiv ℝ p 0) 0 :=
    ((IsQuadraticPolynomial_contDiff hp 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  simpa only [Pi.add_def,sub_add_cancel,zero_add,S] using hz.add hpD.hasFDerivWithinAt

theorem actual_flat_physical_boundary_firstJet_four {lam Lambda alpha Ka Kf B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∀ N : E, ‖N‖=1 → ∃ R > 0, ∃ C > 0, ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ D : ActualFlatLinearInputFour N lam Lambda alpha Ka Kf B, |D.source 0| ≤ F →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        HasFDerivWithinAt D.solution (fderiv ℝ p 0) {x : E | 0 ≤ inner ℝ N x} 0 ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = -D.source 0) ∧
        (∀ v : E, fderiv ℝ p 0 v=inner ℝ N v*fderiv ℝ p 0 N) ∧
        ∀ x : E, 0 ≤ inner ℝ N x → ‖x‖ < R/2 →
          |D.solution x-p x| ≤ M*‖x‖^2*‖x‖^beta := by
  obtain ⟨r,hr,hr8,hrp,hexp⟩ := actual_flat_physical_quadratic_expansion_four
    hlam hLambda halpha hKa hKf hB hF
  intro N hN
  obtain ⟨R,hR,hR1,C,hC,hP⟩ := hexp N hN
  obtain ⟨beta,hbeta,hbeta1,M,hM,hrem⟩ := actual_flat_geometric_remainder_holder_four
    hR hr (by linarith : r < 1) hC.le
  refine ⟨R,hR,C,hC,beta,hbeta,hbeta1,M,hM,?_⟩
  intro D hF0
  obtain ⟨p,hp,hp0,hpD,hpH,hpt,herr⟩ := hP D hF0
  have hzero : D.solution 0=p 0 := by
    rw [D.solution_zero 0 (mem_closedBall_self (by norm_num)) (by simp),hp0 0 (by simp)]
  have hpoint := hrem N D.solution p hzero herr
  exact ⟨p,hp,hp0,actual_flat_remainder_hasFDerivWithinAt_four hp hR hM hbeta.le hpoint,
    hpD,hpH,hpt,actual_flat_quadratic_fderiv_normal_four hN hp hp0,hpoint⟩

end PowerConvexity
