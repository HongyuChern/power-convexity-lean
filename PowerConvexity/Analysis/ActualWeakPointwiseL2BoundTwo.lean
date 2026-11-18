import PowerConvexity.Analysis.ActualSmoothEnergyReplacementTwo

/-! # Pointwise L2-to-sup control for the actual continuous weak solution.
Both signs of the weak equation are used. The almost-everywhere Moser
bound is upgraded on the actual open half ball by continuity and the
positive volume of open sets. No pointwise bound is postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_L2_norm_squared_two {U : Set F} {u : F → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) :
    ‖hu.toLp u‖^2 = ∫ x in U, (u x)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  simp only [hx,Real.inner_apply,pow_two]

theorem actual_continuous_ae_upper_bound_two {U : Set F} (hU : IsOpen U)
    {f : F → ℝ} (hf : ContinuousOn f U) {C : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict U, f x ≤ C) : ∀ x ∈ U, f x ≤ C := by
  have he : (fun x => min (f x) C) =ᵐ[volume.restrict U] f := by
    filter_upwards [hb] with x hx
    exact min_eq_left hx
  have hp := Measure.eqOn_open_of_ae_eq he hU (hf.inf continuousOn_const) hf
  intro x hx
  exact min_eq_left_iff.mp (hp hx)

theorem actual_continuous_weak_unitBall_L2_bound_two
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : F) 1)) :
    ∃ C ≥ 0, ∀ u : F → ℝ, IsHomogeneousWeakSolution A.1 u →
      ContinuousOn u (ball (0 : F) (1/2 : ℝ)) →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1),
      ∀ x ∈ ball (0 : F) (1/2 : ℝ), |u x| ≤ C*‖uw.memLp.toLp u‖ := by
  let K : ℝ := CMoser (2+2)*A.1.Λ ^ (((2+2 : ℕ) : ℝ)/2) *
    (2/(2-1 : ℝ)) ^ ((2+2 : ℕ) : ℝ)
  have hKM : 0 ≤ CMoser (2+2) := le_trans (by norm_num) (one_le_C_Moser (d := 2+2))
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hKM (Real.rpow_nonneg A.1.Λ_nonneg _))
    (Real.rpow_nonneg (by norm_num) _)
  refine ⟨Real.sqrt K,Real.sqrt_nonneg _,?_⟩
  intro u hu hc uw
  let P : F → ℝ := fun x => max (u x) 0
  let N : F → ℝ := fun x => max (-u x) 0
  have hP : MemLp P 2 (volume.restrict (ball (0 : F) 1)) := by
    simpa only [P] using uw.memLp.pos_part
  have hN : MemLp N 2 (volume.restrict (ball (0 : F) 1)) := by
    simpa only [N,Pi.neg_apply] using uw.memLp.neg.pos_part
  have hPI : IntegrableOn (fun x => |P x|^2) (ball (0 : F) 1) volume := by
    simpa only [sq_abs,IntegrableOn] using hP.integrable_sq
  have hNI : IntegrableOn (fun x => |N x|^2) (ball (0 : F) 1) volume := by
    simpa only [sq_abs,IntegrableOn] using hN.integrable_sq
  have hsol := isHomogeneousWeakSolution_isSolution hu
  have hp := linfty_subsolution_Moser_two (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) A hsol.1 hPI
  have hn := linfty_subsolution_Moser_two (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) A
    (actual_supersolution_neg_isSubsolution isOpen_ball hsol.2) hNI
  have hIP : (∫ x in ball (0 : F) 1, |P x|^2) ≤ ∫ x in ball (0 : F) 1, (u x)^2 := by
    apply integral_mono hPI uw.memLp.integrable_sq
    intro x
    by_cases hx : 0 ≤ u x
    · simp [P,max_eq_left hx]
    · simp [P,max_eq_right (le_of_not_ge hx),(sq_nonneg (u x))]
  have hIN : (∫ x in ball (0 : F) 1, |N x|^2) ≤ ∫ x in ball (0 : F) 1, (u x)^2 := by
    apply integral_mono hNI uw.memLp.integrable_sq
    intro x
    by_cases hx : u x ≤ 0
    · simp [N,max_eq_left (neg_nonneg.mpr hx)]
    · simp [N,max_eq_right (neg_nonpos.mpr (le_of_not_ge hx)),(sq_nonneg (u x))]
  have hsqae : ∀ᵐ x ∂volume.restrict (ball (0 : F) (1/2 : ℝ)),
      (u x)^2 ≤ K*(∫ y in ball (0 : F) 1, (u y)^2) := by
    filter_upwards [hp,hn] with x hx hy
    change |P x|^2 ≤ K*(∫ y in ball (0 : F) 1, |P y|^2) at hx
    change |N x|^2 ≤ K*(∫ y in ball (0 : F) 1, |N y|^2) at hy
    by_cases hux : 0 ≤ u x
    · have hh := hx.trans (mul_le_mul_of_nonneg_left hIP hK)
      simpa [P,max_eq_left hux] using hh
    · have hh := hy.trans (mul_le_mul_of_nonneg_left hIN hK)
      simpa [N,max_eq_left (neg_nonneg.mpr (le_of_not_ge hux))] using hh
  have hsq := actual_continuous_ae_upper_bound_two isOpen_ball (hc.pow 2) hsqae
  intro x hx
  have hb := hsq x hx
  rw [← actual_scalar_L2_norm_squared_two uw.memLp] at hb
  change (u x)^2 ≤ K*‖uw.memLp.toLp u‖^2 at hb
  have hroot := Real.sq_sqrt hK
  have hright : 0 ≤ Real.sqrt K*‖uw.memLp.toLp u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have he : (Real.sqrt K*‖uw.memLp.toLp u‖)^2 = K*‖uw.memLp.toLp u‖^2 := by
    rw [mul_pow,hroot]
  nlinarith [sq_abs (u x),abs_nonneg (u x)]

end PowerConvexity
