import PowerConvexity.Analysis.ActualBoundaryVanishingH01Two

/-! # Strong H01 approximation of an actual positive boundary barrier -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_positive_boundary_barrier_memH01_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {p : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hpos : ∀ x ∈ U, 0 < p x) (hp0 : ∀ x ∈ frontier U, p x = 0) :
    MemH01 p U := by
  classical
  let φ : ℕ → E → ℝ := fun n => U.indicator (fun x => actualBoundaryValueCutoffTwo n (p x))
  have hC (n : ℕ) : ContDiff ℝ 1 (φ n) :=
    actual_boundary_value_truncation_C1_two hU hp hp0 n
  have hs (n : ℕ) : tsupport (φ n) ⊆ U :=
    actual_boundary_value_truncation_support_two hU hp.continuous hp0 n
  have hc (n : ℕ) : HasCompactSupport (φ n) :=
    hK.of_isClosed_subset (isClosed_tsupport _) ((hs n).trans subset_closure)
  let pw := actualClassicalBoundedWitnessTwo hU hK hp
  let vw (n : ℕ) := actualClassicalBoundedWitnessTwo hU hK (hC n)
  have hv (n : ℕ) : MemH01 (φ n) U := by
    simpa using memW01p_of_memW1p_of_tsupport_subset hU (by norm_num : (1 : ℝ) < 2)
      (by simpa using (vw n).memW1p) (hc n) (hs n)
  have hF : Tendsto (fun n => eLpNorm (fun x => φ n x-p x) 2 (volume.restrict U))
      atTop (𝓝 0) := by
    apply actual_dominated_L2_convergence_two (fun n => (hC n).continuous.aestronglyMeasurable.restrict)
      pw.memLp pw.memLp
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simpa only [φ,Set.indicator_of_mem hx,Real.norm_eq_abs] using
        actual_boundary_value_cutoff_abs_le_two n (p x)
    · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [actual_boundary_value_cutoff_eventually_identity_two (hpos x hx)] with n hn
      simpa only [φ,Set.indicator_of_mem hx,id_eq] using hn.self_of_nhds.symm
  obtain ⟨D,hD,hDbound⟩ := actual_boundary_value_cutoff_deriv_bound_two
  have hG (i : Fin (2+2)) : Tendsto (fun n => eLpNorm
      (fun x => (vw n).weakGrad x i-pw.weakGrad x i) 2 (volume.restrict U)) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (φ n) x (EuclideanSpace.single i 1)-
        fderiv ℝ p x (EuclideanSpace.single i 1)) 2 (volume.restrict U)) atTop (𝓝 0)
    have hfm (n : ℕ) : AEStronglyMeasurable
        (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) (volume.restrict U) :=
      (((hC n).continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable.restrict
    have hpm : MemLp (fun x => fderiv ℝ p x (EuclideanSpace.single i 1)) 2 (volume.restrict U) :=
      pw.weakGrad_component_memLp i
    apply actual_dominated_L2_convergence_two hfm hpm (hpm.const_mul D)
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have he := actual_boundary_value_truncation_fderiv_two hU hp n hx
      change ‖fderiv ℝ (φ n) x (EuclideanSpace.single i 1)‖ ≤
        ‖D*fderiv ℝ p x (EuclideanSpace.single i 1)‖
      rw [show fderiv ℝ (φ n) x = _ from he,ContinuousLinearMap.smul_apply,
        smul_eq_mul,norm_mul,norm_mul,Real.norm_eq_abs D,abs_of_nonneg hD]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hDbound n (p x))
        (norm_nonneg _)
    · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [actual_boundary_value_cutoff_eventually_identity_two (hpos x hx)] with n hn
      have he := actual_boundary_value_truncation_fderiv_two hU hp n hx
      change fderiv ℝ p x (EuclideanSpace.single i 1) = fderiv ℝ (φ n) x (EuclideanSpace.single i 1)
      rw [show fderiv ℝ (φ n) x = _ from he,hn.deriv_eq,deriv_id,one_smul]
  exact actual_memH01_of_strong_W12_limit_two hU pw φ vw hv hF hG

end PowerConvexity
