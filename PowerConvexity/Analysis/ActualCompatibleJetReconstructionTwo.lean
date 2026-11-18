import PowerConvexity.Analysis.ActualQuadraticTwoCenterJetsTwo

/-! # Reconstructing actual C2 derivatives from compatible local jets

The moduli are explicit hypotheses at this analytic interface. They must be
obtained from the two-centre approximation estimates before applying the
theorem to an actual weak solution. No C2 representative is assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_hasFDerivAt_of_remainder_modulus_two
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} {D : V →L[ℝ] W} {x : V} {omega : V → ℝ}
    (hlim : Tendsto omega (𝓝 x) (𝓝 0))
    (hbound : ∀ᶠ y in 𝓝 x,
      ‖f y-f x-D (y-x)‖ ≤ omega y*‖y-x‖) : HasFDerivAt f D x := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro epsilon hepsilon
  filter_upwards [hbound,hlim.eventually (gt_mem_nhds hepsilon)] with y hy he
  exact hy.trans (mul_le_mul_of_nonneg_right he.le (norm_nonneg _))

theorem actual_continuousAt_of_difference_modulus_two
    {V W : Type*} [TopologicalSpace V] [NormedAddCommGroup W]
    {H : V → W} {x : V} {omega : V → ℝ}
    (hlim : Tendsto omega (𝓝 x) (𝓝 0))
    (hbound : ∀ᶠ y in 𝓝 x, ‖H y-H x‖ ≤ omega y) : ContinuousAt H x := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [hbound,hlim.eventually (gt_mem_nhds hepsilon)] with y hy he
  simpa only [dist_eq_norm] using hy.trans_lt he

theorem actual_C2_of_compatible_jet_moduli_two
    {U : Set E} (hU : IsOpen U) (f : E → ℝ)
    (D : E → E →L[ℝ] ℝ) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hmod : ∀ x ∈ U, ∃ omega₀ omega₁ omega₂ : E → ℝ,
      Tendsto omega₀ (𝓝 x) (𝓝 0) ∧ Tendsto omega₁ (𝓝 x) (𝓝 0) ∧
      Tendsto omega₂ (𝓝 x) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 x, y ∈ U →
        ‖f y-f x-D x (y-x)‖ ≤ omega₀ y*‖y-x‖ ∧
        ‖D y-D x-H x (y-x)‖ ≤ omega₁ y*‖y-x‖ ∧
        ‖H y-H x‖ ≤ omega₂ y) :
    ContDiffOn ℝ 2 f U ∧
      (∀ x ∈ U, fderiv ℝ f x = D x) ∧
      ∀ x ∈ U, realHessian f x = H x := by
  have hfirst : ∀ x ∈ U, HasFDerivAt f (D x) x := by
    intro x hx
    obtain ⟨w₀,w₁,w₂,h₀,h₁,h₂,hb⟩ := hmod x hx
    apply actual_hasFDerivAt_of_remainder_modulus_two h₀
    filter_upwards [hb,hU.mem_nhds hx] with y hy hyU
    exact (hy hyU).1
  have hsecond : ∀ x ∈ U, HasFDerivAt D (H x) x := by
    intro x hx
    obtain ⟨w₀,w₁,w₂,h₀,h₁,h₂,hb⟩ := hmod x hx
    apply actual_hasFDerivAt_of_remainder_modulus_two h₁
    filter_upwards [hb,hU.mem_nhds hx] with y hy hyU
    exact (hy hyU).2.1
  have hHC : ContinuousOn H U := by
    intro x hx
    obtain ⟨w₀,w₁,w₂,h₀,h₁,h₂,hb⟩ := hmod x hx
    have hh : ContinuousAt H x := by
      apply actual_continuousAt_of_difference_modulus_two h₂
      filter_upwards [hb,hU.mem_nhds hx] with y hy hyU
      exact (hy hyU).2.2
    exact hh.continuousWithinAt
  have hDC : ContDiffOn ℝ 1 D U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hU.uniqueDiffOn).mpr
    exact ⟨by norm_num,H,contDiffOn_zero.mpr hHC,
      fun x hx => (hsecond x hx).hasFDerivWithinAt⟩
  have hfC : ContDiffOn ℝ 2 f U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hU.uniqueDiffOn).mpr
    exact ⟨by norm_num,D,hDC,fun x hx => (hfirst x hx).hasFDerivWithinAt⟩
  refine ⟨hfC,fun x hx => (hfirst x hx).fderiv,?_⟩
  intro x hx
  have he : fderiv ℝ f =ᶠ[𝓝 x] D := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hfirst y hy).fderiv
  change fderiv ℝ (fderiv ℝ f) x = H x
  rw [he.fderiv_eq,(hsecond x hx).fderiv]

theorem actual_quadratic_fderiv_from_jet_at_two {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (x y : E) :
    fderiv ℝ q y = fderiv ℝ q x+realHessian q x (y-x) := by
  rw [quadratic_fderiv_from_jet_zero hq y,quadratic_fderiv_from_jet_zero hq x,
    quadratic_realHessian_from_jet_zero hq x,map_sub]
  abel

end PowerConvexity
