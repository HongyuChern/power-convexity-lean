import PowerConvexity.Calculus.PoissonKernelBanachFour

/-! # All interior derivative orders of the actual Poisson integral.
Integration is an actual bounded linear map on continuous sphere functions.
Composition with the proved Banach-algebra kernel gives C^n regularity for
every n, retaining merely continuous actual boundary data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
local notation "F" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : F) 1

def sphereContinuousIntegralLinearFour (mu : Measure S) [IsFiniteMeasure mu] :
    C(S,ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∫ xi, g xi ∂mu
  map_add' g h := by
    exact integral_add
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c g := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply,integral_const_mul]

def sphereContinuousIntegralCLMFour (mu : Measure S) [IsFiniteMeasure mu] :
    C(S,ℝ) →L[ℝ] ℝ :=
  (sphereContinuousIntegralLinearFour mu).mkContinuous (mu.real univ) (by
    intro g
    have hh := norm_integral_le_of_norm_le_const (μ := mu)
      (Filter.Eventually.of_forall (fun xi => g.norm_coe_le_norm xi))
    simpa only [sphereContinuousIntegralLinearFour,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using hh)

theorem sphereContinuousIntegralCLMFour_apply (mu : Measure S) [IsFiniteMeasure mu]
    (g : C(S,ℝ)) : sphereContinuousIntegralCLMFour mu g = ∫ xi, g xi ∂mu := rfl

theorem poissonIntegralFour_contDiffAt (mu : Measure S) [IsFiniteMeasure mu]
    {f : S → ℝ} (hf : Continuous f) {x : F} (hx : x ∈ ball (0 : F) 1) (n : ℕ∞ω) :
    ContDiffAt ℝ n (poissonIntegralFour mu f) x := by
  let fc : C(S,ℝ) := ⟨f,hf⟩
  have hc : ContDiffAt ℝ n (fun y => sphereContinuousIntegralCLMFour mu (fc*poissonKernelMapFour y)) x :=
    (sphereContinuousIntegralCLMFour mu).contDiff.contDiffAt.comp x
      (contDiffAt_const.mul (poissonKernelMapFour_contDiffAt hx n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [sphereContinuousIntegralCLMFour_apply]
  unfold poissonIntegralFour
  apply integral_congr_ae
  filter_upwards with xi
  simp only [ContinuousMap.mul_apply,poissonKernelMapFour_apply hy,fc,ContinuousMap.coe_mk]

theorem poissonIntegralFour_contDiffOn (mu : Measure S) [IsFiniteMeasure mu]
    {f : S → ℝ} (hf : Continuous f) (n : ℕ∞ω) :
    ContDiffOn ℝ n (poissonIntegralFour mu f) (ball (0 : F) 1) :=
  fun x hx => (poissonIntegralFour_contDiffAt mu hf hx n).contDiffWithinAt

end PowerConvexity
