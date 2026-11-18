import PowerConvexity.Analysis.ActualGraphShearC1DriftFour

/-! # Actual local Lipschitz constants on a common closed physical ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_C1_closed_ball_lipschitz_four {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiffAt ℝ 1 f 0) :
    ∃ R > 0, R ≤ 1 ∧ ∃ K ≥ 0, ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖f x-f y‖ ≤ K*‖x-y‖ := by
  obtain ⟨K,T,hT,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hT
  let R := min 1 (d/2)
  have hR : 0 < R := lt_min zero_lt_one (half_pos hd)
  have hsub : closedBall (0 : E) R ⊆ T := by
    intro x hx
    apply hball
    have hxR : dist x 0 ≤ R := hx
    have hRd : R ≤ d/2 := min_le_right _ _
    change dist x 0 < d
    linarith
  refine ⟨R,hR,min_le_left _ _,(K : ℝ),K.2,?_⟩
  intro x hx y hy
  simpa only [dist_eq_norm] using hLip.dist_le_mul x (hsub hx) y (hsub hy)

theorem actual_C1_operator_drift_source_bounds_four
    {A : E → (E →L[ℝ] E)} {b : E → E} {f : E → ℝ}
    (hA : ContDiffAt ℝ 1 A 0) (hb : ContDiffAt ℝ 1 b 0) (hf : ContDiffAt ℝ 1 f 0) :
    ∃ R > 0, R ≤ 1 ∧ ∃ Ka ≥ 0, ∃ Kb ≥ 0, ∃ Kf ≥ 0, ∃ Bd ≥ 0,
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R, ‖A x-A y‖ ≤ Ka*‖x-y‖) ∧
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R, ‖b x-b y‖ ≤ Kb*‖x-y‖) ∧
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R, |f x-f y| ≤ Kf*‖x-y‖) ∧
      ∀ x ∈ closedBall (0 : E) R, ‖b x‖ ≤ Bd := by
  obtain ⟨Ra,hRa,hRa1,Ka,hKa,hLA⟩ := actual_C1_closed_ball_lipschitz_four hA
  obtain ⟨Rb,hRb,_,Kb,hKb,hLb⟩ := actual_C1_closed_ball_lipschitz_four hb
  obtain ⟨Rf,hRf,_,Kf,hKf,hLf⟩ := actual_C1_closed_ball_lipschitz_four hf
  let R := min Ra (min Rb Rf)
  have hR : 0 < R := lt_min hRa (lt_min hRb hRf)
  have hRRa : R ≤ Ra := min_le_left _ _
  have hRRb : R ≤ Rb := (min_le_right _ _).trans (min_le_left _ _)
  have hRRf : R ≤ Rf := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R ≤ 1 := hRRa.trans hRa1
  refine ⟨R,hR,hR1,Ka,hKa,Kb,hKb,Kf,hKf,‖b 0‖+Kb,by positivity,?_,?_,?_,?_⟩
  · intro x hx y hy
    exact hLA x (closedBall_subset_closedBall hRRa hx) y (closedBall_subset_closedBall hRRa hy)
  · intro x hx y hy
    exact hLb x (closedBall_subset_closedBall hRRb hx) y (closedBall_subset_closedBall hRRb hy)
  · intro x hx y hy
    simpa only [Real.norm_eq_abs] using
      hLf x (closedBall_subset_closedBall hRRf hx) y (closedBall_subset_closedBall hRRf hy)
  · intro x hx
    have hh := hLb x (closedBall_subset_closedBall hRRb hx) 0 (mem_closedBall_self hRb.le)
    rw [sub_zero] at hh
    have hx1 : ‖x‖ ≤ 1 := (show ‖x‖ ≤ R from by simpa only [mem_closedBall,dist_zero_right] using hx).trans hR1
    exact (norm_le_insert' (b x) (b 0)).trans
      (add_le_add (le_refl _) (hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hKb)))

end PowerConvexity
