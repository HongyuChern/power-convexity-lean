import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Calculus.ClosureJetDifferentiability
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Actual closure jets under a fixed real linear isometry

The constructed fields are literal pullbacks of the given closure jet, with
exact derivative, Hessian and Hessian-difference operator norms. The same
ambient function is composed with the same linear isometry.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_bilinear_isometric_pullback_norm_two
    (L : F ≃ₗᵢ[ℝ] E) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖H.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
      L.toContinuousLinearEquiv.toContinuousLinearMap‖=‖H‖ := by
  simp only [ContinuousLinearMap.bilinearComp,ContinuousLinearMap.opNorm_flip,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem actual_bilinear_isometric_pullback_difference_two
    (L : F ≃ₗᵢ[ℝ] E) (H K : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖H.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap-
      K.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap‖=‖H-K‖ := by
  have he : H.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap-
      K.bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap=
      (H-K).bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [he,actual_bilinear_isometric_pullback_norm_two]

variable {n : ℕ}
local notation "V" => DeGiorgi.AmbientSpace (n+n)

def actualClosureC2JetIsometricPullbackTwo
    (L : V ≃ₗᵢ[ℝ] E) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ClosureC2Jet (fun x => u (L x)) (L ⁻¹' U) := by
  let T := L.toContinuousLinearEquiv.toContinuousLinearMap
  let C : (E →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ V E ℝ).flip T
  have hmap : MapsTo L (closure (L ⁻¹' U)) (closure U) :=
    (show MapsTo L (L ⁻¹' U) U from fun _ hx => hx).closure L.continuous
  have hC : Continuous (fun D : E →L[ℝ] ℝ => D.comp T) := C.continuous
  have hH : Continuous (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.bilinearComp T T) := by
    have he : (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.bilinearComp T T)=
        (fun H => C.comp (H.comp T)) := by
      funext H
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      rfl
    rw [he]
    exact (continuous_id.clm_comp_const T).const_clm_comp C
  refine {
    derivative := fun x => (J.derivative (L x)).comp T
    hessian := fun x => (J.hessian (L x)).bilinearComp T T
    continuous_value := J.continuous_value.comp L.continuous.continuousOn hmap
    continuous_derivative := hC.comp_continuousOn (J.continuous_derivative.comp L.continuous.continuousOn hmap)
    continuous_hessian := hH.comp_continuousOn (J.continuous_hessian.comp L.continuous.continuousOn hmap)
    derivative_eq := ?_
    hessian_eq := ?_
  }
  · intro x hx
    change (J.derivative (L x)).comp T = _
    rw [J.derivative_eq hx]
    exact (((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt.comp x T.hasFDerivAt).fderiv.symm
  · intro x hx
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.bilinearComp_apply,J.hessian_eq hx]
    exact (realHessian_comp_linearIsometry L (hu.contDiffAt (hU.mem_nhds hx)) v w).symm

theorem actual_isometric_closure_jet_derivative_norm_two
    (L : V ≃ₗᵢ[ℝ] E) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x : V) :
    ‖(actualClosureC2JetIsometricPullbackTwo L hU hu J).derivative x‖=‖J.derivative (L x)‖ := by
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv (J.derivative (L x)) L

theorem actual_isometric_closure_jet_hessian_norm_two
    (L : V ≃ₗᵢ[ℝ] E) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x : V) :
    ‖(actualClosureC2JetIsometricPullbackTwo L hU hu J).hessian x‖=‖J.hessian (L x)‖ :=
  actual_bilinear_isometric_pullback_norm_two L _

theorem actual_isometric_closure_jet_hessian_difference_two
    (L : V ≃ₗᵢ[ℝ] E) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x y : V) :
    ‖(actualClosureC2JetIsometricPullbackTwo L hU hu J).hessian x-
      (actualClosureC2JetIsometricPullbackTwo L hU hu J).hessian y‖=
      ‖J.hessian (L x)-J.hessian (L y)‖ :=
  actual_bilinear_isometric_pullback_difference_two L _ _

end PowerConvexity
