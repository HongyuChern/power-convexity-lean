import PowerConvexity.Analysis.PositiveBilinearTopology
import PowerConvexity.Calculus.PowerTransform
import CHS.Calculus.ClosureRegularity

/-! # Positive power Hessian near a boundary point, from exact closure jets

Tangent Hessian positivity is explicit. This lemma does not identify smooth
strict convexity of a set with positive curvature of its boundary.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem powerHessian_positive_near_boundary_of_tangent_positive
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hneg : ∀ y ∈ U, u y < 0) {x : E} (hx : x ∈ closure U) (hux : u x = 0)
    (htan : ∀ v : E, v ≠ 0 → J.derivative x v = 0 → 0 < J.hessian x v v) :
    ∀ᶠ y in 𝓝 x, y ∈ U → ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform u) y v v := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨lam,hlam,hQpos⟩ := exists_rankOne_stabilization_positive (J.hessian x) (J.derivative x) htan
  let Q : E → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    J.hessian y+lam • (J.derivative y).smulRight (J.derivative y)
  have hQc : ContinuousWithinAt Q (closure U) x := by
    have hd := J.continuous_derivative x hx
    have hh := J.continuous_hessian x hx
    have hr : ContinuousWithinAt (fun y =>
        (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (J.derivative y)) (closure U) x :=
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.continuousAt.comp_continuousWithinAt hd
    have hs : ContinuousWithinAt (fun y => (J.derivative y).smulRight (J.derivative y)) (closure U) x :=
      hr.clm_apply hd
    exact hh.add (hs.const_smul lam)
  have hQp : ∀ v : E, v ≠ 0 → 0 < Q x v v := by
    intro v hv
    simpa only [Q,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hQpos v hv
  have heQ := eventually_nhdsWithin_iff.mp (positive_bilinear_eventually_within hQc hQp)
  have hub : -1/(2*lam) < u x := by rw [hux]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have heu := eventually_nhdsWithin_iff.mp
    ((J.continuous_value x hx).tendsto.eventually (lt_mem_nhds hub))
  filter_upwards [heQ,heu] with y hQy huy hy
  have hycl := subset_closure hy
  have hny := hneg y hy
  have hweight : lam ≤ 1/(2*(-u y)) := by
    apply (le_div_iff₀ (by linarith : 0 < 2*(-u y))).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*lam)).mp (huy hycl)
    nlinarith
  intro v hv
  have hpos := hQy hycl v hv
  change 0 < J.hessian y v v+lam*((J.derivative y v)*(J.derivative y v)) at hpos
  rw [J.derivative_eq hy,J.hessian_eq hy] at hpos
  rw [realHessian_powerTransform (hu.contDiffAt (hU.mem_nhds hy)) hny]
  apply mul_pos (sqrtSlope_pos hny)
  have hm := mul_le_mul_of_nonneg_right hweight (sq_nonneg (fderiv ℝ u y v))
  have hh : (fderiv ℝ u y v)*(fderiv ℝ u y v)/(2*(-u y)) =
      (1/(2*(-u y)))*(fderiv ℝ u y v)^2 := by ring
  rw [hh]
  change 0 < realHessian u y v v+(1/(2*(-u y)))*(fderiv ℝ u y v)^2
  change 0 < realHessian u y v v+lam*((fderiv ℝ u y v)*(fderiv ℝ u y v)) at hpos
  nlinarith

end PowerConvexity
