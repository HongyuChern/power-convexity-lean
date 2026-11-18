import PowerConvexity.Analysis.ActualFlatDriftPhysicalNormalizationFour

/-! # One physical threshold works at every smaller scale

The radius threshold and the normalization smallness are selected before the
coefficient field or the solution. The amplitude may depend on the requested
smaller physical radius; all data use that same amplitude and radius.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_all_small_physical_scales_four
    {alpha Ka Kb Kf Bd B F kappa : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKf : 0 ≤ Kf) (hBd : 0 ≤ Bd)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hk : 0 < kappa) :
    ∃ R₀ > 0, R₀ ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∃ a > 0, 1 ≤ a ∧ F ≤ a ∧ B ≤ a*R^2 ∧
        Ka*R^alpha ≤ kappa ∧ Kb*R^alpha ≤ kappa ∧ R*Bd ≤ kappa ∧
        a⁻¹*Kf*R^alpha ≤ kappa := by
  obtain ⟨R₀,hR₀,hR₀1,a₀,ha₀,ha₀1,ha₀F,hB₀,hKa₀,hKb₀,hBd₀,hKf₀⟩ :=
    actual_flat_drift_physical_scale_four halpha halpha1 hKa hKb hKf hBd hB hF hk
  refine ⟨R₀,hR₀,hR₀1,?_⟩
  intro R hR hRR₀
  let a := max a₀ (B/R^2)
  have ha₀a : a₀ ≤ a := le_max_left _ _
  have ha : 0 < a := ha₀.trans_le ha₀a
  have hpow : R^alpha ≤ R₀^alpha := Real.rpow_le_rpow hR.le hRR₀ halpha.le
  have hsize : B ≤ a*R^2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hR)).mp (le_max_right a₀ (B/R^2))
    exact hh
  have hinv : a⁻¹ ≤ a₀⁻¹ := inv_anti₀ ha₀ ha₀a
  have hsource : a⁻¹*Kf*R^alpha ≤ kappa := by
    calc
      _ ≤ a₀⁻¹*Kf*R₀^alpha := mul_le_mul
        (mul_le_mul_of_nonneg_right hinv hKf) hpow
        (Real.rpow_nonneg hR.le _) (mul_nonneg (inv_nonneg.mpr ha₀.le) hKf)
      _ ≤ kappa := hKf₀
  exact ⟨a,ha,ha₀1.trans ha₀a,ha₀F.trans ha₀a,hsize,
    (mul_le_mul_of_nonneg_left hpow hKa).trans hKa₀,
    (mul_le_mul_of_nonneg_left hpow hKb).trans hKb₀,
    (mul_le_mul_of_nonneg_right hRR₀ hBd).trans hBd₀,hsource⟩

theorem actual_flat_drift_common_normalization_all_scales_four
    {alpha Ka Kb Kf Bd B F kappa : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKf : 0 ≤ Kf) (hBd : 0 ≤ Bd)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hk : 0 < kappa) :
    ∃ R₀ > 0, R₀ ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∃ a > 0, 1 ≤ a ∧ F ≤ a ∧
      ∀ N : E, ∀ lam Lambda : ℝ,
      ∀ D : ActualFlatDriftPhysicalInputFour N lam Lambda alpha Ka Kb Kf Bd B,
      ∃ D' : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa,
        D'.solution=normalizedScalarResidualTwo D.solution (fun _ => 0) R a ∧
        D'.drift=(fun z => R • D.drift (R • z)) ∧
        D'.source=(fun z => a⁻¹*D.source (R • z)) := by
  obtain ⟨R₀,hR₀,hR₀1,hsmall⟩ := actual_flat_drift_all_small_physical_scales_four
    halpha halpha1 hKa hKb hKf hBd hB hF hk
  refine ⟨R₀,hR₀,hR₀1,?_⟩
  intro R hR hRR₀
  obtain ⟨a,ha,ha1,haF,hsize,hca,hcb,hbd,hs⟩ := hsmall R hR hRR₀
  refine ⟨a,ha,ha1,haF,?_⟩
  intro N lam Lambda D
  refine ⟨actualFlatDriftPhysicalNormalizeFour hR (hRR₀.trans hR₀1) ha hKb D
    hca hcb hbd hs hsize,rfl,rfl,?_⟩
  funext z
  exact actual_flat_drift_zero_residual_source_four D.coeff.a D.drift D.source R a z

end PowerConvexity
