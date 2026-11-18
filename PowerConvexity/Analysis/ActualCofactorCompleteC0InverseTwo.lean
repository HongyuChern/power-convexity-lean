import PowerConvexity.Analysis.ActualContinuousWeakResponseTwo
import PowerConvexity.Calculus.ActualPhysicalC0InverseTwo

/-! # The same actual cofactor inverse for every continuous load

The complete C0 operator is constructed from the genuine Dirichlet solves.
Its value on every continuous load is a continuous representative of the
actual zero-trace weak solution.  On C1 loads that same value has C2 interior
regularity and solves the classical linearized equation.  No boundary C2
jet or nonlinear openness is claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_cofactor_complete_C0_dirichlet_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U))
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
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff v x) :
    ∃ T : C(closure U, ℝ) →L[ℝ] C(closure U, ℝ), ‖T‖ ≤ M/2 ∧
      (∀ g : E → ℝ, ∀ hg : ContinuousOn g (closure U), ∃ H : E → ℝ,
        Continuous H ∧ MemH01 H U ∧
        ActualScalarWeakEquationTwo A (fun x => -(c⁻¹*ρ x*g x)) H ∧
        (∀ x ∈ frontier U, H x=0) ∧
        ∀ x : closure U, T ⟨fun y => g y,hg.domRestrict⟩ x=H x) ∧
      ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
        Continuous h ∧ ContDiffOn ℝ 2 h U ∧
        (∀ x ∈ frontier U, h x=0) ∧
        (∀ x ∈ U, linearizedCMAOperatorTwo realDirections imagDirections v h x=g x) ∧
        MemH01 h U ∧ ActualScalarWeakEquationTwo A (fun x => -(c⁻¹*ρ x*g x)) h ∧
        ∀ x : closure U,
          T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
  let L : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.refl ℝ E
  obtain ⟨T,hT,hzero,hclassical⟩ := actual_physical_C0_inverse_two hU hK L
    realDirections imagDirections (fun _ => rfl) (fun _ => rfl)
    hw hwp hwb hv hvC hvb hvp hvd hρ hρlo hc hM hvM A hA
  refine ⟨T,hT,?_,hclassical⟩
  intro g hg
  let d : E → ℝ := fun x => c⁻¹*ρ x
  have hd : ContinuousOn d (closure U) := continuousOn_const.mul hρ.continuous.continuousOn
  have hd0 : ∀ x ∈ U, 0 ≤ d x := by
    intro x hx
    exact mul_nonneg (inv_nonneg.mpr hc.le) ((by norm_num : (0 : ℝ) ≤ 1).trans (hρlo x hx))
  have hcl : ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
      Continuous h ∧ MemH01 h U ∧ ActualScalarWeakEquationTwo A (fun x => -(d x*g x)) h ∧
      ∀ x : closure U, T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
    intro g hg
    obtain ⟨h,hhC,hh2,hhb,hhPDE,hh0,hhw,hhT⟩ := hclassical g hg
    exact ⟨h,hhC,hh0,hhw,hhT⟩
  exact actual_continuous_load_weak_response_two hU hK A hd hd0 T hzero hcl hg

end PowerConvexity
