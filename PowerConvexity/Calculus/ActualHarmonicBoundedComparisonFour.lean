import PowerConvexity.Calculus.ViscosityHarmonicBallUniquenessTwo

/-! # Actual harmonic comparison on arbitrary bounded open subsets of R4
The strict barrier is the same explicit enclosing-ball quadratic. This will
be used on genuine half balls, whose flat boundary cannot be discarded.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_harmonic_bounded_comparison_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {g p : E → ℝ} (hgc : ContinuousOn g (closure U)) (hg : IsViscosityHarmonicTwo g U)
    (hpc : ContinuousOn p (closure U)) (hp : ContDiffOn ℝ 2 p U)
    (ht : ∀ x ∈ U, (realBlockHessian realDirections imagDirections p x).trace ≤ 0)
    (hb : ∀ x ∈ frontier U, g x ≤ p x) : ∀ x ∈ closure U, g x ≤ p x := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  intro x hx
  by_contra hbad
  have hgap : 0 < g x-p x := sub_pos.mpr (lt_of_not_ge hbad)
  let delta : ℝ := (g x-p x)/(2*(R^2+1))
  have hden : 0 < 2*(R^2+1) := by positivity
  have hd : 0 < delta := div_pos hgap hden
  have hdeq : delta*(2*(R^2+1))=g x-p x := div_mul_cancel₀ _ hden.ne'
  let P : E → ℝ := fun y => p y+translatedBallPotential (-delta) R 0 y
  have hPC : ContinuousOn P (closure U) := hpc.add
    (translatedBallPotential_contDiff (-delta) R (0 : E) 2).continuous.continuousOn
  have hP2 : ContDiffOn ℝ 2 P U := hp.add
    (translatedBallPotential_contDiff (-delta) R (0 : E) 2).contDiffOn
  have hPt (y : E) (hy : y ∈ U) :
      (realBlockHessian realDirections imagDirections P y).trace < 0 := by
    rw [show P = fun z => p z+translatedBallPotential (-delta) R 0 z from rfl,
      actual_C2_block_trace_add_ball_potential_two (hp.contDiffAt (hU.mem_nhds hy))]
    linarith only [ht y hy,hd]
  have hPb (y : E) (hy : y ∈ frontier U) : g y ≤ P y := by
    have hn := hbound y (frontier_subset_closure hy)
    have hn2 : ‖y‖^2 ≤ R^2 := by nlinarith [norm_nonneg y]
    have hnon : 0 ≤ translatedBallPotential (-delta) R (0 : E) y := by
      simp only [translatedBallPotential,quadraticBallPotential,sub_zero]
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hn2)]
    exact (hb y hy).trans (le_add_of_nonneg_right hnon)
  have hh := viscosity_harmonic_le_strict_classical_superharmonic_two
    hU hK hgc hg hPC hP2 hPt hPb x hx
  have hn : 0 ≤ delta*‖x‖^2 := mul_nonneg hd.le (sq_nonneg _)
  dsimp only [P,translatedBallPotential,quadraticBallPotential] at hh
  simp only [sub_zero] at hh
  nlinarith only [hh,hdeq,hn,hd]

theorem actual_harmonic_bounded_uniqueness_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {g p : E → ℝ} (hgc : ContinuousOn g (closure U))
    (hg : InnerProductSpace.HarmonicOnNhd g U)
    (hpc : ContinuousOn p (closure U)) (hp : InnerProductSpace.HarmonicOnNhd p U)
    (hb : EqOn g p (frontier U)) : EqOn g p (closure U) := by
  have hgp := actual_harmonic_bounded_comparison_four hU hK hgc
    (classical_harmonic_isViscosityHarmonicTwo hg) hpc hp.contDiffOn
    (fun x hx => (actual_classical_harmonic_trace_zero_two hp hx).le) (fun x hx => (hb hx).le)
  have hpg := actual_harmonic_bounded_comparison_four hU hK hpc
    (classical_harmonic_isViscosityHarmonicTwo hp) hgc hg.contDiffOn
    (fun x hx => (actual_classical_harmonic_trace_zero_two hg hx).le) (fun x hx => (hb hx).ge)
  exact fun x hx => le_antisymm (hgp x hx) (hpg x hx)

end PowerConvexity
