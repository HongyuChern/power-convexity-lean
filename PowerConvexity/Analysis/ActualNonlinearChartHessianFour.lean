import PowerConvexity.Analysis.ActualLinearHessianTransportFour
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # The genuine second chain rule for a nonlinear boundary chart -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_nonlinear_chart_hessian_four {u : E → ℝ} {Phi : E → E} {x : E}
    (hu : ContDiffAt ℝ 2 u (Phi x)) (hPhi : ContDiffAt ℝ 2 Phi x) (v w : E) :
    realHessian (u ∘ Phi) x v w =
      realHessian u (Phi x) (fderiv ℝ Phi x v) (fderiv ℝ Phi x w)+
        fderiv ℝ u (Phi x) (fderiv ℝ (fderiv ℝ Phi) x v w) := by
  have huE : ∀ᶠ y : E in 𝓝 x, ContDiffAt ℝ 1 u (Phi y) :=
    hPhi.continuousAt.tendsto.eventually ((hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num))
  have hpE : ∀ᶠ y : E in 𝓝 x, ContDiffAt ℝ 1 Phi y :=
    (hPhi.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have heq : fderiv ℝ (u ∘ Phi) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u (Phi y)).comp (fderiv ℝ Phi y)) := by
    filter_upwards [huE,hpE] with y huy hpy
    exact fderiv_comp y (huy.differentiableAt (by norm_num)) (hpy.differentiableAt (by norm_num))
  have hdPhi := (hPhi.differentiableAt (by norm_num)).hasFDerivAt
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hdDPhi := ((hPhi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := (hdu.comp x hdPhi).clm_comp hdDPhi
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  have hh := hh.trans (by simpa only [Function.comp_def] using hc.fderiv)
  have hvw := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) hh
  simpa only [realHessian,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_comm] using hvw

end PowerConvexity
