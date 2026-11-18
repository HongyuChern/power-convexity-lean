import PowerConvexity.Analysis.ActualC1WeakDivergenceTestsTwo
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual weak divergence survives a commonly bounded pointwise limit

The vector fields and sources are eventually continuous and commonly
bounded on the true closed ball. Dominated convergence is applied to the
actual compact smooth test pairings; no derivatives of the fields are used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_hasWeakDiv_of_common_bounded_limit_two
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {c : E} {r : ℝ} {F : ι → E → E} {g : ι → E → ℝ}
    {F₀ : E → E} {g₀ : E → ℝ}
    (hdiv : ∀ᶠ n in l, HasWeakDiv (g n) (F n) (ball c r))
    (hcont : ∀ᶠ n in l,
      (∀ i, ContinuousOn (fun x => F n x i) (closedBall c r)) ∧
      ContinuousOn (g n) (closedBall c r))
    (hbound : ∃ C ≥ 0, ∀ᶠ n in l, ∀ x ∈ closedBall c r,
      ‖F n x‖ ≤ C ∧ |g n x| ≤ C)
    (hFlim : ∀ x ∈ ball c r, Tendsto (fun n => F n x) l (𝓝 (F₀ x)))
    (hglim : ∀ x ∈ ball c r, Tendsto (fun n => g n x) l (𝓝 (g₀ x))) :
    HasWeakDiv g₀ F₀ (ball c r) := by
  letI : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  intro phi hphi hpc hps
  obtain ⟨C,hC,hbound⟩ := hbound
  have hphiD : Continuous (fderiv ℝ phi) := hphi.continuous_fderiv (by simp)
  obtain ⟨B₀,hB₀⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hphi.continuous.continuousOn
  obtain ⟨B₁,hB₁⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hphiD.continuousOn
  let B := max B₀ 0+max B₁ 0+1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hvalue (x : E) (hx : x ∈ closedBall c r) : |phi x| ≤ B := by
    have hh := hB₀ x hx
    rw [Real.norm_eq_abs] at hh
    dsimp only [B]
    linarith [le_max_left B₀ 0,le_max_right B₁ 0]
  have hderivative (x : E) (hx : x ∈ closedBall c r) (i : Fin (2+2)) :
      |fderiv ℝ phi x (EuclideanSpace.single i 1)| ≤ B := by
    have hh := (fderiv ℝ phi x).le_opNorm (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp only [B]; linarith [hB₁ x hx,le_max_left B₁ 0,le_max_right B₀ 0])
  let L : ι → E → ℝ := fun n x => ∑ i, F n x i*fderiv ℝ phi x (EuclideanSpace.single i 1)
  let L₀ : E → ℝ := fun x => ∑ i, F₀ x i*fderiv ℝ phi x (EuclideanSpace.single i 1)
  have hLm : ∀ᶠ n in l, AEStronglyMeasurable (L n) (volume.restrict (ball c r)) := by
    filter_upwards [hcont] with n hn
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_ball
    apply continuousOn_finsetSum
    intro i _
    exact ((hn.1 i).mono ball_subset_closedBall).mul
      ((hphiD.clm_apply continuous_const).continuousOn)
  have hLb : ∀ᶠ n in l, ∀ᵐ x ∂(volume.restrict (ball c r)), ‖L n x‖ ≤ 4*C*B := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxC := ball_subset_closedBall hx
    calc
      _ ≤ ∑ i : Fin (2+2), ‖F n x i*fderiv ℝ phi x (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (2+2), C*B := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using
          (PiLp.norm_apply_le (F n x) i).trans (hn x hxC).1)
          (hderivative x hxC i) (abs_nonneg _) hC
      _ = 4*C*B := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hLl : ∀ᵐ x ∂(volume.restrict (ball c r)), Tendsto (fun n => L n x) l (𝓝 (L₀ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    apply tendsto_finsetSum
    intro i _
    have hFi : Tendsto (fun n => F n x i) l (𝓝 (F₀ x i)) :=
      (PiLp.continuous_apply 2 (fun _ : Fin (2+2) => ℝ) i).continuousAt.tendsto.comp (hFlim x hx)
    exact hFi.mul_const _
  have hLint := tendsto_integral_filter_of_norm_le_const hLm ⟨4*C*B,hLb⟩ hLl
  have hRm : ∀ᶠ n in l, AEStronglyMeasurable (fun x => g n x*phi x) (volume.restrict (ball c r)) := by
    filter_upwards [hcont] with n hn
    exact (((hn.2.mono ball_subset_closedBall).mul hphi.continuous.continuousOn).aestronglyMeasurable measurableSet_ball)
  have hRb : ∀ᶠ n in l, ∀ᵐ x ∂(volume.restrict (ball c r)), ‖g n x*phi x‖ ≤ C*B := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact mul_le_mul (hn x (ball_subset_closedBall hx)).2
      (hvalue x (ball_subset_closedBall hx)) (abs_nonneg _) hC
  have hRl : ∀ᵐ x ∂(volume.restrict (ball c r)),
      Tendsto (fun n => g n x*phi x) l (𝓝 (g₀ x*phi x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hglim x hx).mul_const _
  have hRint := tendsto_integral_filter_of_norm_le_const hRm ⟨C*B,hRb⟩ hRl
  have he : (fun n => ∫ x in ball c r, L n x) =ᶠ[l]
      (fun n => -(∫ x in ball c r, g n x*phi x)) := by
    filter_upwards [hdiv] with n hn
    exact hn phi hphi hpc hps
  exact tendsto_nhds_unique hLint (hRint.neg.congr' he.symm)

end PowerConvexity
