import PowerConvexity.Calculus.ParameterGraphLocalInverse

/-! # Actual space derivatives of a jointly smooth parameter function -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem parameter_fiber_fderiv_eq
    {F : ℝ × E → G} {p : ℝ × E} (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ (fun y => F (p.1,y)) p.2 =
      (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
  (hF.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

theorem parameter_fiber_fderiv_contDiffAt
    {F : ℝ × E → G} {p : ℝ × E} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ (n+1) F p) :
    ContDiffAt ℝ n (fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2) p := by
  have h1 : ContDiffAt ℝ 1 F p := hF.of_le (by simp)
  have heq : (fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2) =ᶠ[𝓝 p]
      (fun q => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    filter_upwards [h1.eventually (by norm_num)] with q hq
    exact parameter_fiber_fderiv_eq (hq.differentiableAt (by norm_num))
  exact ((hF.fderiv_right le_rfl).clm_comp contDiffAt_const).congr_of_eventuallyEq heq

theorem parameter_fiber_fderiv_eventually_ne_zero
    {F : ℝ × E → G} {p : ℝ × E} (hF : ContDiffAt ℝ 2 F p)
    (hD : fderiv ℝ (fun y => F (p.1,y)) p.2 ≠ 0) :
    ∀ᶠ q : ℝ × E in 𝓝 p, fderiv ℝ (fun y => F (q.1,y)) q.2 ≠ 0 :=
  (parameter_fiber_fderiv_contDiffAt (n := 1) hF).continuousAt.tendsto.eventually
    (eventually_ne_nhds hD)

end PowerConvexity
