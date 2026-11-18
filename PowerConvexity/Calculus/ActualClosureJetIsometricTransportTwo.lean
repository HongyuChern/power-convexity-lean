import PowerConvexity.Analysis.ActualUniformIsometricClosureJetTwo

/-! # Actual closure jets transported between arbitrary isometric ambient spaces -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_realHessian_comp_isometric_two
    (T : F ≃ₗᵢ[ℝ] E) {u : E → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u (T x)) (v w : F) :
    realHessian (fun y => u (T y)) x v w=realHessian u (T x) (T v) (T w) := by
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using realHessian_comp_affine
    T.toContinuousLinearEquiv.toContinuousLinearMap 0 (x := x)
    (by simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hu) v w

def actualClosureC2JetIsometricTransportTwo
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V)
    (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ClosureC2Jet (fun x => u (T x)) V := by
  let L := T.toContinuousLinearEquiv.toContinuousLinearMap
  let C : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  have hmap : MapsTo T V U := by intro x hx; rwa [← hUV] at hx
  have hmapc : MapsTo T (closure V) (closure U) := hmap.closure T.continuous
  have hC : Continuous (fun D : E →L[ℝ] ℝ => D.comp L) := C.continuous
  have hH : Continuous (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.bilinearComp L L) := by
    have he : (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.bilinearComp L L)=
        (fun H => C.comp (H.comp L)) := by
      funext H
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      rfl
    rw [he]
    exact (continuous_id.clm_comp_const L).const_clm_comp C
  refine {
    derivative := fun x => (J.derivative (T x)).comp L
    hessian := fun x => (J.hessian (T x)).bilinearComp L L
    continuous_value := J.continuous_value.comp T.continuous.continuousOn hmapc
    continuous_derivative := hC.comp_continuousOn (J.continuous_derivative.comp T.continuous.continuousOn hmapc)
    continuous_hessian := hH.comp_continuousOn (J.continuous_hessian.comp T.continuous.continuousOn hmapc)
    derivative_eq := ?_
    hessian_eq := ?_ }
  · intro x hx
    change (J.derivative (T x)).comp L=_
    rw [J.derivative_eq (hmap hx)]
    exact (((hu.contDiffAt (hU.mem_nhds (hmap hx))).differentiableAt (by norm_num)).hasFDerivAt.comp x
      L.hasFDerivAt).fderiv.symm
  · intro x hx
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.bilinearComp_apply,J.hessian_eq (hmap hx)]
    exact (actual_realHessian_comp_isometric_two T (hu.contDiffAt (hU.mem_nhds (hmap hx))) v w).symm

theorem actualClosureC2JetIsometricTransportTwo_derivative_norm
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V)
    (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x : F) :
    ‖(actualClosureC2JetIsometricTransportTwo U V T hUV hU hu J).derivative x‖=‖J.derivative (T x)‖ :=
  ContinuousLinearMap.opNorm_comp_linearIsometryEquiv (J.derivative (T x)) T

theorem actualClosureC2JetIsometricTransportTwo_hessian_norm
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V)
    (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x : F) :
    ‖(actualClosureC2JetIsometricTransportTwo U V T hUV hU hu J).hessian x‖=‖J.hessian (T x)‖ :=
  actual_bilinear_isometric_pullback_norm_two T _

theorem actualClosureC2JetIsometricTransportTwo_hessian_difference
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V)
    (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (x y : F) :
    ‖(actualClosureC2JetIsometricTransportTwo U V T hUV hU hu J).hessian x-
      (actualClosureC2JetIsometricTransportTwo U V T hUV hU hu J).hessian y‖=
      ‖J.hessian (T x)-J.hessian (T y)‖ :=
  actual_bilinear_isometric_pullback_difference_two T _ _

end PowerConvexity
