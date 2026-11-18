import PowerConvexity.Analysis.ZeroTracePoincareLp
import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual L2 scalar forcing for weak zero-Dirichlet problems.
The load is the actual integral of f times the test function. Its boundedness
is proved from Cauchy-Schwarz and the zero-trace Poincare estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology RealInnerProductSpace
namespace PowerConvexity
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem continuous_memLp_two_of_subset_compact
    {U K : Set E} (hK : IsCompact K) (hUK : U ⊆ K)
    {f : E → ℝ} (hf : Continuous f) : MemLp f 2 (volume.restrict U) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  exact ((hf.pow 2).continuousOn.integrableOn_compact hK).mono_set hUK

theorem scalar_L2_integral_mul_bound {U : Set E} {f g : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    |∫ x in U, f x*g x| ≤ ‖hf.toLp f‖*‖hg.toLp g‖ := by
  have he : (∫ x in U, f x*g x) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
    simp only [hfx,hgx,Real.inner_apply]
  rw [he]
  exact abs_real_inner_le_norm _ _

theorem scalar_weak_dirichlet_exists
    {U : Set E} (hd : 2 ≤ d) (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (A : EllipticCoeff d U) {f : E → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    ∃ u : E → ℝ, IsWeakSolution ⟨U,hU,hb,A,(fun phi => ∫ x in U, f x*phi x)⟩ u ∧
      ∀ v : E → ℝ, IsWeakSolution ⟨U,hU,hb,A,(fun phi => ∫ x in U, f x*phi x)⟩ v →
        u =ᵐ[volume.restrict U] v := by
  obtain ⟨C,hC,hP⟩ := zeroTrace_poincare_L2_witness_bound hd hU hb
  have hex : ∃ u : E → ℝ,
      IsWeakSolution ⟨U,hU,hb,A,(fun phi => ∫ x in U, f x*phi x)⟩ u := by
    apply weakProblem_exists hd hU hb A (fun phi => ∫ x in U, f x*phi x)
    · intro u v hu hv
      simp only [mul_add]
      exact integral_add (hf.integrable_mul hu.1.1) (hf.integrable_mul hv.1.1)
    · intro c u hu
      have he : (fun x => f x*(c*u x)) = (fun x => c*(f x*u x)) := by
        funext x
        ring
      rw [he,integral_const_mul]
    · refine ⟨‖hf.toLp f‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
      intro v hv hw
      have hh := (scalar_L2_integral_mul_bound hf hw.memLp).trans
        (mul_le_mul_of_nonneg_left (hP v hv hw) (norm_nonneg (hf.toLp f)))
      simpa only [norm_gradLpOfWitness_eq,mul_assoc] using hh
  obtain ⟨u,hu⟩ := hex
  exact ⟨u,hu,fun v hv => weakProblem_unique hd hu hv⟩

end PowerConvexity
