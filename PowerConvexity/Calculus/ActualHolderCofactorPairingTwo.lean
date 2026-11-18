import PowerConvexity.Calculus.ActualHolderComplexFieldTwo
import PowerConvexity.Calculus.CofactorLinearizedDirichletTwo

/-! # Exact raw cofactor pairing and injectivity on the actual Holder jet space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] actualDensityJetSeminormed

theorem actual_complex_cofactor_hessian_contraction_two
    {v h : E → ℝ} {x : E} (hh : ContDiffAt ℝ 2 h x) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (complexHessian realDirections imagDirections v x).adjugate j i*
      complexHessian realDirections imagDirections h x i j).re =
      ∑ i, ∑ j, complexCofactorCoeff v x i j*euclideanHessian h x i j := by
  rw [realLinearizationMatrix_pairing hh realDirections imagDirections
    (complexHessian realDirections imagDirections v x).adjugate]
  symm
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp_rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexCofactorCoeff,realLinearizedWeight,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,euclideanHessian,← blockDirection_eq_single,realBlockHessian]

theorem actualHolderDeterminantDerivativeTwo_eq_cofactor
    {U : Set E} [CompactSpace (closure U)] (hU : IsOpen U) (alpha : ℝ)
    (p q : actualHolderC2JetSpaceTwo U alpha) {x : E} (hx : x ∈ U) :
    actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
      (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p q)
      ⟨x,subset_closure hx⟩ =
      ∑ i, ∑ j, complexCofactorCoeff (actualClosureExtensionTwo U p.1.1) x i j*
        euclideanHessian (actualClosureExtensionTwo U q.1.1) x i j := by
  rw [actualHolderDeterminantDerivativeTwo_apply]
  change (∑ i : Fin 2, ∑ j : Fin 2,
    (actualHolderComplexFieldTwo U alpha realDirections imagDirections p ⟨x,subset_closure hx⟩).adjugate j i*
    actualHolderComplexFieldTwo U alpha realDirections imagDirections q ⟨x,subset_closure hx⟩ i j).re = _
  rw [actualHolderComplexFieldTwo_eq_actual U hU alpha realDirections imagDirections p hx,
    actualHolderComplexFieldTwo_eq_actual U hU alpha realDirections imagDirections q hx]
  exact actual_complex_cofactor_hessian_contraction_two
    ((actualHolderC2JetSpaceTwo_regular U hU alpha q).1.contDiffAt (hU.mem_nhds hx))

theorem actualHolderDeterminantDerivativeTwo_injective
    {U : Set E} [CompactSpace (closure U)] (hU : IsOpen U) (hK : IsCompact (closure U))
    (alpha : ℝ) (p : actualHolderC2JetSpaceTwo U alpha)
    (hp : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).PosDef) :
    Function.Injective (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p) := by
  let L := actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p
  have hker : ∀ q : actualHolderC2JetSpaceTwo U alpha, L q=0 → q=0 := by
    intro q hq
    let v := actualClosureExtensionTwo U p.1.1
    let u := actualClosureExtensionTwo U q.1.1
    have hcof : ∀ x ∈ U, (∑ i, ∑ j, complexCofactorCoeff v x i j*euclideanHessian u x i j)=0 := by
      intro x hx
      have he := actualHolderDeterminantDerivativeTwo_eq_cofactor hU alpha p q hx
      change actualHolderLoadSpaceTwo_value _ _ alpha (L q) ⟨x,subset_closure hx⟩=_ at he
      rw [hq,map_zero,ContinuousMap.zero_apply] at he
      exact he.symm
    have hlinear : ∀ x ∈ U, linearizedCMAOperatorTwo realDirections imagDirections v u x=0 := by
      intro x hx
      have he := complexCofactor_contraction_eq_density_linearized_two (hp x hx) u
      rw [hcof x hx] at he
      exact (mul_eq_zero.mp he.symm).resolve_left (Complex.pos_iff.mp (hp x hx).det_pos).1.ne'
    have hz := linearizedCMAOperatorTwo_zero_kernel realDirections imagDirections hU hK
      (actualClosureExtensionTwo_continuousOn U p.1.1) (actualHolderC2JetSpaceTwo_regular U hU alpha p).1
      p.2.2.2 hp (actualClosureExtensionTwo_continuousOn U q.1.1)
      (actualHolderC2JetSpaceTwo_regular U hU alpha q).1 q.2.2.2 hlinear
    apply actualHolderC2JetSpaceTwo_value_injective U hU alpha
    apply ContinuousMap.ext
    intro x
    change q.1.1 x=0
    have hh := hz x.property
    rw [actualClosureExtensionTwo_apply U q.1.1 x.property] at hh
    exact hh
  intro q r hqr
  have he : L (q-r)=0 := (map_sub L q r).trans (sub_eq_zero.mpr hqr)
  exact sub_eq_zero.mp (hker (q-r) he)

end PowerConvexity
