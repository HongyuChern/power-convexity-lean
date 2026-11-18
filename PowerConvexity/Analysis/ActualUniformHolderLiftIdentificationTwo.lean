import PowerConvexity.Calculus.ActualHolderC2JetLiftTwo
import PowerConvexity.Calculus.ActualHolderComplexFieldTwo
import PowerConvexity.Calculus.ClosureVariableDensity
import PowerConvexity.Calculus.CMAJetsIsometricTransport

/-! # Exact derivative and equation identification for an actual Holder lift

Equality of the true closure values forces both derivative fields to agree
with the same given closure jet. This identifies the strict branch and the
nonlinear determinant equation in the complete Holder spaces.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable (U : Set E) [CompactSpace (closure U)]

theorem actual_holder_lift_derivative_fields_two
    (hU : IsOpen U) (alpha : ℝ) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (p : actualHolderC2JetSpaceTwo U alpha)
    (hp : actualHolderC2JetSpaceTwo_value U alpha p=⟨fun x => u x,J.continuous_value.domRestrict⟩) :
    (∀ x : closure U, actualHolderC2JetSpaceTwo_gradient U alpha p x=J.derivative x) ∧
      ∀ x : closure U,
        actualHolderLoadSpaceTwo_value _ _ alpha (actualHolderC2JetSpaceTwo_hessian U alpha p) x=J.hessian x := by
  obtain ⟨hp2,Jp,hJD,hJH⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have he (x : E) (hx : x∈U) : actualClosureExtensionTwo U p.1.1=ᶠ[𝓝 x] u := by
    filter_upwards [hU.mem_nhds hx] with y hy
    change actualClosureExtensionTwo U (actualHolderC2JetSpaceTwo_value U alpha p) y=u y
    rw [hp,actualClosureExtensionTwo_apply U _ (subset_closure hy)]
    rfl
  have hDi : EqOn Jp.derivative J.derivative U := by
    intro x hx
    rw [Jp.derivative_eq hx,J.derivative_eq hx]
    exact (he x hx).fderiv_eq
  have hHi : EqOn Jp.hessian J.hessian U := by
    intro x hx
    rw [Jp.hessian_eq hx,J.hessian_eq hx]
    exact realHessian_eq_of_eventuallyEq (he x hx)
  have hDcl := hDi.of_subset_closure Jp.continuous_derivative J.continuous_derivative
    subset_closure (Subset.rfl : closure U ⊆ closure U)
  have hHcl := hHi.of_subset_closure Jp.continuous_hessian J.continuous_hessian
    subset_closure (Subset.rfl : closure U ⊆ closure U)
  constructor
  · intro x
    have hh := hDcl x.property
    rw [hJD,actualClosureExtensionTwo_apply U _ x.property] at hh
    exact hh
  · intro x
    have hh := hHcl x.property
    rw [hJH,actualClosureExtensionTwo_apply U _ x.property] at hh
    exact hh

theorem actual_holder_lift_variable_density_equation_two
    (hU : IsOpen U) (alpha : ℝ) (a b : Fin 2 → E)
    {u rho : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hrho : ContinuousOn rho (closure U)) (hrho0 : ∀ x ∈ closure U, rho x≠0)
    (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det=(rho x : ℂ))
    (q : actualHolderLoadSpaceTwo (closure U) ℝ alpha)
    (hq : ∀ x : closure U, actualHolderLoadSpaceTwo_value (closure U) ℝ alpha q x=rho x)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (hp : actualHolderC2JetSpaceTwo_value U alpha p=⟨fun x => u x,J.continuous_value.domRestrict⟩) :
    (∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) ∧
      actualHolderDeterminantTwo U alpha a b p=q := by
  have hfields := actual_holder_lift_derivative_fields_two U hU alpha hu J p hp
  have hfield (x : closure U) : actualHolderComplexFieldTwo U alpha a b p x=J.complexField a b x := by
    unfold actualHolderComplexFieldTwo
    rw [hfields.2 x]
    rfl
  have hC : ContinuousOn (fun x => (rho x : ℂ)) (closure U) :=
    Complex.continuous_ofReal.comp_continuousOn hrho
  have hdetcl := closure_complexField_variableDensity J hU hu a b hC hdet
  constructor
  · intro x
    rw [hfield]
    exact closure_complexField_posDef_of_variableDensity J hU hu a b hC
      (fun y hy => Complex.ofReal_ne_zero.mpr (hrho0 y hy)) hdet hpos x x.property
  · apply actualHolderLoadSpaceTwo_value_injective (closure U) ℝ alpha
    apply ContinuousMap.ext
    intro x
    rw [actualHolderDeterminantTwo_apply,hq]
    change (actualHolderComplexFieldTwo U alpha a b p x).det.re=rho x
    rw [hfield,hdetcl x x.property,Complex.ofReal_re]

end PowerConvexity
