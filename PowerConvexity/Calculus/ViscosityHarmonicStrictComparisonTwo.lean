import PowerConvexity.Calculus.SmallCMAUniformLimitLocalTestsTwo

/-! # Actual boundary comparison against strict classical barriers.
The viscosity function need only be continuous on the actual closed
domain. An actual compact maximum supplies the interior test contact.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem viscosity_harmonic_le_strict_classical_superharmonic_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {g p : E → ℝ} (hgc : ContinuousOn g (closure U)) (hg : IsViscosityHarmonicTwo g U)
    (hpc : ContinuousOn p (closure U)) (hp : ContDiffOn ℝ 2 p U)
    (htrace : ∀ x ∈ U, (realBlockHessian realDirections imagDirections p x).trace < 0)
    (hboundary : ∀ x ∈ frontier U, g x ≤ p x) :
    ∀ x ∈ closure U, g x ≤ p x := by
  intro x hx
  by_contra hbad
  have hxpos : 0 < g x-p x := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨y,hy,hm⟩ := hK.exists_isMaxOn ⟨x,hx⟩ (hgc.sub hpc)
  have hmax := hm hx
  change g x-p x ≤ g y-p y at hmax
  have hyU : y ∈ U := by
    by_contra hyout
    have hyF : y ∈ frontier U := by
      rw [frontier,hU.interior_eq]
      exact ⟨hy,hyout⟩
    have hb := hboundary y hyF
    linarith only [hb,hmax,hxpos]
  have hlocal : IsLocalMin (fun z => p z-g z) y := by
    change ∀ᶠ z in 𝓝 y, p y-g y ≤ p z-g z
    filter_upwards [hU.mem_nhds hyU] with z hz
    have hh := hm (subset_closure hz)
    change g z-p z ≤ g y-p y at hh
    linarith only [hh]
  have ht := (hg.2 y hyU p (hp.contDiffAt (hU.mem_nhds hyU))).2 hlocal
  exact (not_le_of_gt (htrace y hyU)) ht

theorem strict_classical_subharmonic_le_viscosity_harmonic_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {g p : E → ℝ} (hgc : ContinuousOn g (closure U)) (hg : IsViscosityHarmonicTwo g U)
    (hpc : ContinuousOn p (closure U)) (hp : ContDiffOn ℝ 2 p U)
    (htrace : ∀ x ∈ U, 0 < (realBlockHessian realDirections imagDirections p x).trace)
    (hboundary : ∀ x ∈ frontier U, p x ≤ g x) :
    ∀ x ∈ closure U, p x ≤ g x := by
  intro x hx
  by_contra hbad
  have hxpos : 0 < p x-g x := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨y,hy,hm⟩ := hK.exists_isMaxOn ⟨x,hx⟩ (hpc.sub hgc)
  have hmax := hm hx
  change p x-g x ≤ p y-g y at hmax
  have hyU : y ∈ U := by
    by_contra hyout
    have hyF : y ∈ frontier U := by
      rw [frontier,hU.interior_eq]
      exact ⟨hy,hyout⟩
    have hb := hboundary y hyF
    linarith only [hb,hmax,hxpos]
  have hlocal : IsLocalMin (fun z => g z-p z) y := by
    change ∀ᶠ z in 𝓝 y, g y-p y ≤ g z-p z
    filter_upwards [hU.mem_nhds hyU] with z hz
    have hh := hm (subset_closure hz)
    change p z-g z ≤ p y-g y at hh
    linarith only [hh]
  have ht := (hg.2 y hyU p (hp.contDiffAt (hU.mem_nhds hyU))).1 hlocal
  exact (not_le_of_gt (htrace y hyU)) ht

end PowerConvexity
