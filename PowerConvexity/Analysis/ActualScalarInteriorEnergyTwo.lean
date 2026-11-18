import PowerConvexity.Analysis.ActualScalarCaccioppoliTwo
import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo

/-! # Actual interior gradient energy from scalar L2 data.
One fixed smooth cutoff is selected before the coefficient and solution.
The estimate is for the actual restricted Sobolev gradient witness.
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

theorem actual_gradLp_norm_squared_two {U : Set F} {u : F → ℝ}
    (uw : MemW1pWitness 2 u U) :
    ‖gradLpOfWitness uw‖^2 = ∫ x in U, ‖uw.weakGrad x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [uw.weakGrad_memLp.coeFn_toLp] with x hx
  change ⟪uw.weakGrad_memLp.toLp uw.weakGrad x,uw.weakGrad_memLp.toLp uw.weakGrad x⟫_ℝ = _
  rw [hx,real_inner_self_eq_norm_sq]

theorem actual_scalar_unitBall_gradient_bound_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ K > 0, ∀ A : NormalizedEllipticCoeff (2+2) (ball (0 : F) 1), A.1.Λ ≤ L →
      ∀ f u : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : F) 1)),
      ActualScalarWeakEquationTwo A.1 f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1),
      ‖gradLpOfWitness (uw.restrict isOpen_ball (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)))‖^2 ≤
        K*(‖uw.memLp.toLp u‖^2+‖hf.toLp f‖^2) := by
  let b : ContDiffBump (0 : F) := ⟨1/2,3/4,by norm_num,by norm_num⟩
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  have hDc : HasCompactSupport (fderiv ℝ b) := b.hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C0,hC0⟩ := hDc.isCompact.exists_bound_of_continuousOn
    (hb.continuous_fderiv (by simp)).continuousOn
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hDb (x : F) : ‖fderiv ℝ b x‖ ≤ C := by
    by_cases hx : x ∈ tsupport (fderiv ℝ b)
    · exact (hC0 x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
      exact hC
  have hbb (x : F) : |b x| ≤ 1 := by rw [abs_of_nonneg b.nonneg]; exact b.le_one
  have hbs : tsupport b ⊆ ball (0 : F) 1 := by
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 1)
  let K := 1+4*L^2*C^2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro A hAL f u hf hu uw
  have he := actual_scalar_cutoff_energy_two isOpen_ball A hf hu uw hb
    b.hasCompactSupport hbs hbb hC hDb
  have hgI := uw.weakGrad_norm_memLp.integrable_sq
  have hwI : Integrable (fun x => (b x)^2*‖uw.weakGrad x‖^2)
      (volume.restrict (ball (0 : F) 1)) := by
    apply Integrable.mono' hgI
    · exact ((hb.continuous.pow 2).aestronglyMeasurable.mul hgI.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun x => by
        have hh : (b x)^2 ≤ 1 := by nlinarith [b.nonneg (x := x),b.le_one (x := x)]
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖uw.weakGrad x‖])
  have heq : (∫ x in ball (0 : F) (1/2 : ℝ), ‖uw.weakGrad x‖^2) =
      ∫ x in ball (0 : F) (1/2 : ℝ), (b x)^2*‖uw.weakGrad x‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hbx : b x = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hx)
    rw [hbx,one_pow,one_mul]
  have hm := setIntegral_mono_set hwI
    (ae_of_all _ (fun x => by positivity : ∀ x : F, 0 ≤ (b x)^2*‖uw.weakGrad x‖^2))
    (ae_of_all _ (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)))
  have hmain := (le_of_eq heq).trans (hm.trans he)
  rw [actual_gradLp_norm_squared_two]
  change (∫ x in ball (0 : F) (1/2 : ℝ), ‖uw.weakGrad x‖^2) ≤ _
  rw [actual_scalar_L2_norm_squared_two,actual_scalar_L2_norm_squared_two]
  have hs : A.1.Λ^2 ≤ L^2 := (sq_le_sq₀ A.1.Λ_nonneg hL).mpr hAL
  have hk : 1+4*A.1.Λ^2*C^2 ≤ K := by
    dsimp only [K]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg C)]
  have hIu : 0 ≤ ∫ x in ball (0 : F) 1, (u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have hIf : 0 ≤ ∫ x in ball (0 : F) 1, (f x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have hK1 : 1 ≤ K := by
    have hh : 0 ≤ 4*L^2*C^2 := by positivity
    dsimp only [K]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hk hIu,mul_le_mul_of_nonneg_right hK1 hIf]

end PowerConvexity
