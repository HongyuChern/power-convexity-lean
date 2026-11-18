import PowerConvexity.Analysis.ActualHolderWeakResponseClassicalTwo
import PowerConvexity.Analysis.ActualContinuousDomainBoundaryDataFour

/-! # Actual domain data for every complete Holder load of the same weak response

The coefficients, weight and bounded C0 operator are fixed before the load.
The domain data below use the actual weighted source and the actual value of
that same operator. Interior classical regularity is proved by the weak
continuous-source Schauder theorem, rather than assumed as a field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualHolderWeakResponseDataTwo
    (U : Set E) [CompactSpace (closure U)] (alpha Ka Kd Bd : ℝ) where
  coeff : EllipticCoeff (2+2) U
  positive : ∀ x ∈ U, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) U
  divergence : ∀ x ∈ U, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ closure U, ∀ y ∈ closure U,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤ Ka*‖x-y‖^alpha
  weight : E → ℝ
  weight_continuous : ContinuousOn weight (closure U)
  weight_bound : ∀ x ∈ closure U, |weight x| ≤ Bd
  weight_holder : ∀ x ∈ closure U, ∀ y ∈ closure U,
    |weight x-weight y| ≤ Kd*‖x-y‖^alpha
  operator : C(closure U,ℝ) →L[ℝ] C(closure U,ℝ)
  weak : ∀ g : C(closure U,ℝ), ∃ H : E → ℝ,
    ActualScalarWeakEquationTwo coeff (fun x => -(weight x*actualClosureExtensionTwo U g x)) H ∧
    ∀ x : closure U, operator g x=H x
  zero : ∀ g : C(closure U,ℝ), ∀ (x : E) (hx : x ∈ frontier U),
    operator g ⟨x,frontier_subset_closure hx⟩=0

def ActualHolderWeakResponseDataTwo.domainData
    {U : Set E} [CompactSpace (closure U)] {alpha Ka Kd Bd : ℝ}
    (D : ActualHolderWeakResponseDataTwo U alpha Ka Kd Bd)
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (g : actualHolderLoadSpaceTwo (closure U) ℝ alpha) :
    ActualContinuousDomainLinearDataFour U D.coeff.lam D.coeff.Λ alpha Ka ((Kd+Bd)*‖g‖) where
  coeff := D.coeff
  source := fun x => -(D.weight x*actualClosureExtensionTwo U
    (actualHolderLoadSpaceTwo_value _ _ alpha g) x)
  solution := actualClosureExtensionTwo U (D.operator (actualHolderLoadSpaceTwo_value _ _ alpha g))
  lower := le_rfl
  upper := le_rfl
  positive := D.positive
  regular := D.regular
  divergence := D.divergence
  holder := D.holder
  source_continuous := (actual_holder_load_weighted_bounds_two hKd hBd
    D.weight_continuous D.weight_bound D.weight_holder g).1.mono subset_closure
  source_holder := (actual_holder_load_weighted_bounds_two hKd hBd
    D.weight_continuous D.weight_bound D.weight_holder g).2.2
  solution_regular := (actual_holder_weak_response_classical_two hU hK D.coeff D.positive
    D.regular D.divergence halpha halpha1 hKa hKd hBd D.holder
    D.weight_continuous D.weight_bound D.weight_holder D.operator D.weak g).2.1
  solution_continuous := actualClosureExtensionTwo_continuousOn U _
  equation := by
    intro x hx
    simpa only [neg_neg] using (actual_holder_weak_response_classical_two hU hK D.coeff D.positive
      D.regular D.divergence halpha halpha1 hKa hKd hBd D.holder
      D.weight_continuous D.weight_bound D.weight_holder D.operator D.weak g).2.2 x hx

theorem ActualHolderWeakResponseDataTwo.domainData_bounds
    {U : Set E} [CompactSpace (closure U)] {alpha Ka Kd Bd : ℝ}
    (D : ActualHolderWeakResponseDataTwo U alpha Ka Kd Bd)
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (g : actualHolderLoadSpaceTwo (closure U) ℝ alpha) :
    let Q := D.domainData hU hK halpha halpha1 hKa hKd hBd g
    (∀ x ∈ closure U, |Q.source x| ≤ Bd*‖g‖) ∧
      (∀ x ∈ closure U, |Q.solution x| ≤ ‖D.operator‖*‖g‖) ∧
      ∀ x ∈ frontier U, Q.solution x=0 := by
  refine ⟨(actual_holder_load_weighted_bounds_two hKd hBd
    D.weight_continuous D.weight_bound D.weight_holder g).2.1,?_,?_⟩
  · intro x hx
    change |actualClosureExtensionTwo U (D.operator (actualHolderLoadSpaceTwo_value _ _ alpha g)) x| ≤ _
    rw [actualClosureExtensionTwo_apply U _ hx]
    exact (((D.operator (actualHolderLoadSpaceTwo_value _ _ alpha g)).norm_coe_le_norm ⟨x,hx⟩).trans
      (D.operator.le_opNorm _)).trans (mul_le_mul_of_nonneg_left
        (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha g) (norm_nonneg _))
  · intro x hx
    change actualClosureExtensionTwo U (D.operator (actualHolderLoadSpaceTwo_value _ _ alpha g)) x=0
    rw [actualClosureExtensionTwo_apply U _ (frontier_subset_closure hx)]
    exact D.zero _ x hx

end PowerConvexity
