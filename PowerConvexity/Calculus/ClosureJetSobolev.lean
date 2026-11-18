import PowerConvexity.Analysis.LocalClassicalWeakDerivatives
import CHS.Calculus.ClosureRegularity
import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual closure jets give actual L2 Sobolev witnesses.
Only compactness of the closure and C1 regularity inside are used. The
gradient of an AE-equal raw weak function is identified with the actual
classical gradient on the open domain.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem continuousOn_memLp_two_of_subset_compact
    {U K : Set E} (hU : MeasurableSet U) (hK : IsCompact K) (hUK : U ⊆ K)
    {f : E → ℝ} (hf : ContinuousOn f K) : MemLp f 2 (volume.restrict U) := by
  apply (memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable_of_subset_isCompact hK hU hUK)).2
  exact ((hf.pow 2).integrableOn_compact hK).mono_set hUK

def closureJetSobolevWitness
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {H : E → ℝ} (hH : ContDiffOn ℝ 1 H U) (J : ClosureC2Jet H U) :
    MemW1pWitness 2 H U where
  memLp := continuousOn_memLp_two_of_subset_compact hU.measurableSet hK
    subset_closure J.continuous_value
  weakGrad := fun x => WithLp.toLp 2 (fun i => J.derivative x (EuclideanSpace.single i 1))
  weakGrad_component_memLp := by
    intro i
    exact continuousOn_memLp_two_of_subset_compact hU.measurableSet hK
      subset_closure (J.continuous_derivative.clm_apply continuousOn_const)
  isWeakGrad := by
    intro i phi hp hpc hps
    rw [hasWeakPartialDeriv_of_contDiffOn hU hH i phi hp hpc hps]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [PiLp.toLp_apply,J.derivative_eq hx]

theorem closureJet_weakGradient_eq_classical_ae
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {H h : E → ℝ} (hH : ContDiffOn ℝ 1 H U) (J : ClosureC2Jet H U)
    (he : H =ᵐ[volume.restrict U] h) (hw : MemW1pWitness 2 h U) :
    hw.weakGrad =ᵐ[volume.restrict U] smoothGradField H := by
  let hW := closureJetSobolevWitness hU hK hH J
  have hi (i : Fin d) : (fun x => hw.weakGrad x i) =ᵐ[volume.restrict U]
      (fun x => hW.weakGrad x i) :=
    HasWeakPartialDeriv.ae_eq hU
      (hasWeakPartialDeriv_congr_value_ae he.symm (hw.isWeakGrad i)) (hW.isWeakGrad i)
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hW.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr hi,ae_restrict_mem hU.measurableSet] with x hx hxU
  ext i
  rw [hx i]
  simp only [hW,closureJetSobolevWitness,PiLp.toLp_apply,smoothGradField,J.derivative_eq hxU]

end PowerConvexity
