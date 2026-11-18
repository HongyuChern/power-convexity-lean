import PowerConvexity.Calculus.ActualHolderDeterminantIsometricTwo
import PowerConvexity.Calculus.ContinuousLinearConjugacyInverse

/-! # Transfer of the actual bounded determinant inverse

Both identities follow from the proved determinant derivative intertwining
and the two genuine complete-space isomorphisms. No new PDE is postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  holderResponseJetSeminormedGroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_holder_determinant_inverse_isometric_two
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (a b : Fin 2 → E) (ha : ∀ i, T (realDirections i)=a i)
    (hb : ∀ i, T (imagDirections i)=b i)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (S : actualHolderLoadSpaceTwo (closure V) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo V alpha)
    (hSright : (actualHolderDeterminantDerivativeTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)).comp S=
        ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure V) ℝ alpha))
    (hSleft : S.comp (actualHolderDeterminantDerivativeTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p))=
        ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo V alpha)) :
    ∃ R : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderDeterminantDerivativeTwo U alpha a b p).comp R=
        ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) ∧
      R.comp (actualHolderDeterminantDerivativeTwo U alpha a b p)=
        ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo U alpha) := by
  exact actual_bounded_inverse_of_linear_conjugacy
    (X := actualHolderC2JetSpaceTwo U alpha)
    (Y := actualHolderC2JetSpaceTwo V alpha)
    (V := actualHolderLoadSpaceTwo (closure U) ℝ alpha)
    (W := actualHolderLoadSpaceTwo (closure V) ℝ alpha)
    (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha)
    (actualHolderLoadIsometricEquivTwo U V T hUV alpha)
    (actualHolderDeterminantDerivativeTwo U alpha a b p)
    (actualHolderDeterminantDerivativeTwo V alpha realDirections imagDirections
      (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p)) S
    (actual_holder_determinant_derivative_isometric_two U V hU hV T hUV alpha a b ha hb p)
    hSright hSleft

end PowerConvexity
