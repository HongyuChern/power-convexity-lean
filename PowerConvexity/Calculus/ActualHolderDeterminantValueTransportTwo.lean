import PowerConvexity.Calculus.ActualHolderIsometricTransportTwo
import PowerConvexity.Calculus.ActualHolderComplexFieldTwo
import PowerConvexity.Calculus.CMAJetsIsometricTransport

/-! # Value-based identification of an actually transported determinant

The potential and load are arbitrary actual Holder elements.  Their values
identify the transported determinant through genuine local differentiation
and extension by continuity.  Keeping these elements as parameters avoids
unfolding the choice construction of the Banach-space isometries.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
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

theorem actual_holder_determinant_transport_of_actual_values_two
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (a b : Fin 2 → E) (ha : ∀ i, T (realDirections i)=a i)
    (hb : ∀ i, T (imagDirections i)=b i)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (q : actualHolderC2JetSpaceTwo V alpha)
    (g : actualHolderLoadSpaceTwo (closure V) ℝ alpha)
    (hvalue : ∀ x ∈ V, actualClosureExtensionTwo V q.1.1 x=
      actualClosureExtensionTwo U p.1.1 (T x))
    (hload : ∀ x ∈ V, actualClosureExtensionTwo V
      (actualHolderLoadSpaceTwo_value (closure V) ℝ alpha g) x=
      actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
        (actualHolderDeterminantTwo U alpha a b p)) (T x)) :
    actualHolderDeterminantTwo V alpha realDirections imagDirections q=g := by
  let u := actualClosureExtensionTwo U p.1.1
  let v := actualClosureExtensionTwo V q.1.1
  have hu := (actualHolderC2JetSpaceTwo_regular U hU alpha p).1
  have hv := (actualHolderC2JetSpaceTwo_regular V hV alpha q).1
  have hH (x : F) (hx : x∈V) : complexHessian realDirections imagDirections v x=
      complexHessian a b u (T x) := by
    have hmap : T x∈U := by rwa [←hUV] at hx
    have he : v =ᶠ[𝓝 x] (fun y => u (T y)) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact hvalue y hy
    have hh : realHessian v x=realHessian (fun y => u (T y)) x := he.fderiv.fderiv_eq
    have huT : ContDiffAt ℝ 2 (fun y => u (T y)) x :=
      (hu.contDiffAt (hU.mem_nhds hmap)).comp x T.contDiff.contDiffAt
    rw [←actualDirectedComplexHessianFormTwo_eq realDirections imagDirections
      (hv.contDiffAt (hV.mem_nhds hx)),hh,
      actualDirectedComplexHessianFormTwo_eq realDirections imagDirections huT,
      complexHessian_comp_linearIsometry T (hu.contDiffAt (hU.mem_nhds hmap))]
    rw [show (fun i => T (realDirections i))=a from funext ha,
      show (fun i => T (imagDirections i))=b from funext hb]
  let f := actualHolderLoadSpaceTwo_value (closure V) ℝ alpha
    (actualHolderDeterminantTwo V alpha realDirections imagDirections q)
  let k := actualHolderLoadSpaceTwo_value (closure V) ℝ alpha g
  have he : EqOn (actualClosureExtensionTwo V f) (actualClosureExtensionTwo V k) V := by
    intro x hx
    have hmap : T x∈U := by rwa [←hUV] at hx
    have hk := hload x hx
    change actualClosureExtensionTwo V k x=_ at hk
    rw [hk,actualClosureExtensionTwo_apply V f (subset_closure hx),
      actualClosureExtensionTwo_apply U _ (subset_closure hmap)]
    exact (actualHolderDeterminantTwo_eq_actual V hV alpha realDirections imagDirections q hx).trans
      ((congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det.re) (hH x hx)).trans
        (actualHolderDeterminantTwo_eq_actual U hU alpha a b p hmap).symm)
  have hec := he.of_subset_closure (actualClosureExtensionTwo_continuousOn V f)
    (actualClosureExtensionTwo_continuousOn V k) subset_closure (Subset.rfl : closure V⊆closure V)
  apply actualHolderLoadSpaceTwo_value_injective (closure V) ℝ alpha
  apply ContinuousMap.ext
  intro x
  change f x=k x
  simpa only [actualClosureExtensionTwo_apply V f x.property,
    actualClosureExtensionTwo_apply V k x.property] using hec x.property


end PowerConvexity
