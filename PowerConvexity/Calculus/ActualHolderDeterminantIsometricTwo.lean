import PowerConvexity.Calculus.ActualHolderIsometricTransportTwo
import PowerConvexity.Calculus.ActualHolderComplexFieldTwo
import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Calculus.ActualHolderDeterminantValueTransportTwo
import PowerConvexity.Calculus.ContinuousLinearConjugacyDerivative

/-! # The actual nonlinear determinant commutes with its isometric transport

The same complete Holder jet is transported by its actual values. Interior
derivative uniqueness identifies its complex Hessian, and continuity extends
the actual determinant identity to the whole closure. Differentiating this
identity gives the exact intertwining of the two actual Frechet derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "F" => AmbientSpace (2+2)
variable (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
  (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
  (a b : Fin 2 → E) (ha : ∀ i, T (realDirections i)=a i)
  (hb : ∀ i, T (imagDirections i)=b i)
include ha hb

theorem actual_holder_jet_isometric_complex_hessian_two
    (p : actualHolderC2JetSpaceTwo U alpha) {x : F} (hx : x∈V) :
    complexHessian realDirections imagDirections
      (actualClosureExtensionTwo V (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p).1.1) x=
      complexHessian a b (actualClosureExtensionTwo U p.1.1) (T x) := by
  let P := actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha
  let u := actualClosureExtensionTwo U p.1.1
  let v := actualClosureExtensionTwo V (P p).1.1
  have hmap : T x∈U := by rwa [←hUV] at hx
  have hu := (actualHolderC2JetSpaceTwo_regular U hU alpha p).1
  have hv := (actualHolderC2JetSpaceTwo_regular V hV alpha (P p)).1
  have he : v =ᶠ[𝓝 x] (fun y => u (T y)) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact actualHolderJetIsometricEquivTwo_apply_value U V hU hV T hUV alpha p (subset_closure hy)
  have hH : realHessian v x=realHessian (fun y => u (T y)) x :=
    he.fderiv.fderiv_eq
  have huT : ContDiffAt ℝ 2 (fun y => u (T y)) x :=
    (hu.contDiffAt (hU.mem_nhds hmap)).comp x T.contDiff.contDiffAt
  change complexHessian realDirections imagDirections v x=complexHessian a b u (T x)
  rw [←actualDirectedComplexHessianFormTwo_eq realDirections imagDirections
    (hv.contDiffAt (hV.mem_nhds hx)),hH,
    actualDirectedComplexHessianFormTwo_eq realDirections imagDirections huT,
    complexHessian_comp_linearIsometry T (hu.contDiffAt (hU.mem_nhds hmap))]
  rw [show (fun i => T (realDirections i))=a from funext ha,
    show (fun i => T (imagDirections i))=b from funext hb]

theorem actual_holder_determinant_isometric_two
    (p : actualHolderC2JetSpaceTwo U alpha) :
    actualHolderDeterminantTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)=
      actualHolderLoadIsometricEquivTwo U V T hUV alpha
        (actualHolderDeterminantTwo U alpha a b p) := by
  exact actual_holder_determinant_transport_of_actual_values_two U V hU hV T hUV alpha a b ha hb p
    (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)
    (actualHolderLoadIsometricEquivTwo U V T hUV alpha (actualHolderDeterminantTwo U alpha a b p))
    (fun x hx => actualHolderJetIsometricEquivTwo_apply_value U V hU hV T hUV alpha p (subset_closure hx))
    (fun x hx => actualHolderLoadIsometricEquivTwo_apply_value U V T hUV alpha _ (subset_closure hx))

theorem actual_holder_determinant_derivative_isometric_two
    (p : actualHolderC2JetSpaceTwo U alpha) :
    (actualHolderDeterminantDerivativeTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)).comp
        (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha).toContinuousLinearMap=
      (actualHolderLoadIsometricEquivTwo U V T hUV alpha).toContinuousLinearMap.comp
        (actualHolderDeterminantDerivativeTwo U alpha a b p) := by
  exact actual_derivative_intertwine_of_linear_conjugacy
    (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha).toContinuousLinearMap
    (actualHolderLoadIsometricEquivTwo U V T hUV alpha).toContinuousLinearMap
    (actualHolderDeterminantTwo U alpha a b)
    (actualHolderDeterminantTwo V alpha realDirections imagDirections) p
    (actualHolderDeterminantDerivativeTwo U alpha a b p)
    (actualHolderDeterminantDerivativeTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p))
    (actualHolderDeterminantTwo_hasStrictFDerivAt U alpha a b p).hasFDerivAt
    (actualHolderDeterminantTwo_hasStrictFDerivAt V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)).hasFDerivAt
    (actual_holder_determinant_isometric_two U V hU hV T hUV alpha a b ha hb)

end PowerConvexity
