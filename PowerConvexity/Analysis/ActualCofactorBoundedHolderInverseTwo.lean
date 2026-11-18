import PowerConvexity.Analysis.ActualSmoothDomainHolderResponseTwo
import PowerConvexity.Analysis.ActualCofactorHolderResponseDataTwo
import PowerConvexity.Calculus.ActualHolderCofactorPairingTwo

/-! # The actual bounded cofactor inverse between complete Holder spaces

The source space is the full C^{0,alpha} graph space. The target is the
complete space of actual zero-boundary C2 jets with alpha-Holder Hessian.
Boundary expansions and global Schauder regularity are proved from the
actual smooth defining geometry. The final theorem identifies both inverse
identities with the genuine Frechet derivative of the complex determinant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] holderResponseJetSeminormedGroup

theorem actual_scaled_matrix_contraction_cancel_two
    {A B H : Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {c g : ℝ}
    (hc : 0 < c) (hA : A=c⁻¹ • B)
    (heq : (∑ i, ∑ j, A i j*H i j)=c⁻¹*g) :
    (∑ i, ∑ j, B i j*H i j)=g := by
  have hh : c⁻¹*(∑ i, ∑ j, B i j*H i j)=c⁻¹*g := by
    simpa only [hA,Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum] using heq
  exact mul_left_cancel₀ (inv_ne_zero hc.ne') hh

theorem actual_cofactor_bounded_holder_response_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {r₀ diameter alpha Ka : ℝ}
    (hr₀ : 0 < r₀) (hdia : 0 ≤ diameter)
    (hball : closedBall o r₀ ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    {phi : E → ℝ} (hphi : ContDiff ℝ 3 phi)
    (hphi0 : ∀ c ∈ frontier U, phi c=0) (hDphi : ∀ c ∈ frontier U, fderiv ℝ phi c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ phi z < 0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hKa : 0 ≤ Ka)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x=0)
    {v ρ : E → ℝ} (hv : ContDiffOn ℝ 4 v U)
    (hvC : ContinuousOn v (closure U)) (hvb : ∀ x ∈ frontier U, v x=0)
    (hvp : ∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef)
    (hvd : ∀ x ∈ U, (complexHessian realDirections imagDirections v x).det=(ρ x : ℂ))
    (hρ : ContDiff ℝ 1 ρ) (hρlo : ∀ x ∈ U, 1 ≤ ρ x)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hvM : ∀ x ∈ closure U, -v x ≤ M)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff v x)
    (hAH : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha) :
    ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      ∀ g : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      let u := actualClosureExtensionTwo U (actualHolderC2JetSpaceTwo_value U alpha (S g))
      let f := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha g)
      ActualScalarWeakEquationTwo A (fun x => -(c⁻¹*f x)) u ∧ ContDiffOn ℝ 2 u U ∧
        ∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j)=c⁻¹*f x := by
  have hDex := actual_cofactor_holder_weak_response_data_two hU hK hw hwp hwb hv hvC hvb
    hvp hvd hρ hρlo hc hM hvM A hA hAH
  let D := Classical.choose hDex
  have hD := Classical.choose_spec hDex
  have hDA : D.coeff=A := hD.1
  have hDw : D.weight=(fun _ => c⁻¹) := hD.2.1
  have hSex := actual_smooth_domain_bounded_holder_response_two hU hK hproper hconv hr₀ hdia
    hball hdiam hphi hphi0 hDphi hdef halpha halpha1 hKa (by norm_num : (0 : ℝ) ≤ 0)
    (inv_nonneg.mpr hc.le) D
  let S := Classical.choose hSex
  have hS := (Classical.choose_spec hSex).1
  refine ⟨S,?_⟩
  intro g
  have he := actual_holder_lifted_response_equation_two hU hK halpha halpha1 hKa
    (by norm_num : (0 : ℝ) ≤ 0) (inv_nonneg.mpr hc.le) D S hS g
  simpa only [hDA,hDw] using he

theorem actual_holder_determinant_derivative_bounded_inverse_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {r₀ diameter alpha Ka : ℝ}
    (hr₀ : 0 < r₀) (hdia : 0 ≤ diameter)
    (hball : closedBall o r₀ ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    {phi : E → ℝ} (hphi : ContDiff ℝ 3 phi)
    (hphi0 : ∀ c ∈ frontier U, phi c=0) (hDphi : ∀ c ∈ frontier U, fderiv ℝ phi c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ phi z < 0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hKa : 0 ≤ Ka)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x=0)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (hv : ContDiffOn ℝ 4 (actualClosureExtensionTwo U p.1.1) U)
    (hvp : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).PosDef)
    {ρ : E → ℝ}
    (hvd : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).det=(ρ x : ℂ))
    (hρ : ContDiff ℝ 1 ρ) (hρlo : ∀ x ∈ U, 1 ≤ ρ x)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hvM : ∀ x ∈ closure U, -actualClosureExtensionTwo U p.1.1 x ≤ M)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff (actualClosureExtensionTwo U p.1.1) x)
    (hAH : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha) :
    ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p).comp S=
        ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) ∧
      S.comp (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p)=
        ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo U alpha) := by
  have hSex := actual_cofactor_bounded_holder_response_two hU hK hproper hconv hr₀ hdia hball hdiam
    hphi hphi0 hDphi hdef halpha halpha1 hKa hw hwp hwb hv
    (actualClosureExtensionTwo_continuousOn U p.1.1) p.2.2.2 hvp hvd hρ hρlo hc hM hvM A hA hAH
  let S := Classical.choose hSex
  have hS := Classical.choose_spec hSex
  let L := actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p
  have hright : L.comp S=ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) := by
    apply ContinuousLinearMap.ext
    intro g
    apply actualHolderLoadSpaceTwo_value_injective (closure U) ℝ alpha
    let F := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha (L (S g))
    let G := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha g
    have he : EqOn (actualClosureExtensionTwo U F) (actualClosureExtensionTwo U G) U := by
      intro x hx
      rw [actualClosureExtensionTwo_apply U F (subset_closure hx),
        actualClosureExtensionTwo_apply U G (subset_closure hx)]
      change actualHolderLoadSpaceTwo_value _ _ alpha (L (S g)) ⟨x,subset_closure hx⟩=G ⟨x,subset_closure hx⟩
      rw [actualHolderDeterminantDerivativeTwo_eq_cofactor hU alpha p (S g) hx]
      have heq := (hS g).2.2 x hx
      have hvalue : actualClosureExtensionTwo U G x=G ⟨x,subset_closure hx⟩ :=
        actualClosureExtensionTwo_apply U G (subset_closure hx)
      exact actual_scaled_matrix_contraction_cancel_two hc (hA x hx)
        (heq.trans (congrArg (fun t : ℝ => c⁻¹*t) hvalue))
    have heC := he.of_subset_closure (actualClosureExtensionTwo_continuousOn U F)
      (actualClosureExtensionTwo_continuousOn U G) subset_closure (Subset.rfl : closure U ⊆ closure U)
    apply ContinuousMap.ext
    intro x
    change F x=G x
    simpa only [actualClosureExtensionTwo_apply U F x.property,
      actualClosureExtensionTwo_apply U G x.property] using heC x.property
  refine ⟨S,hright,?_⟩
  apply ContinuousLinearMap.ext
  intro q
  apply actualHolderDeterminantDerivativeTwo_injective hU hK alpha p hvp
  have he := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ]
    actualHolderLoadSpaceTwo (closure U) ℝ alpha => Q (L q)) hright
  exact he

end PowerConvexity
