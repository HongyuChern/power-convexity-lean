import PowerConvexity.Analysis.ActualContinuousPhysicalWeakResponseTwo
import PowerConvexity.Calculus.ActualPhysicalC0InverseTwo

/-! # The complete physical C0 inverse is the actual weak inverse

Every continuous load gives a continuous representative of the genuine
zero-trace weak solution for the actual normalized cofactor matrix.  On C1
loads, the same bounded operator is the classical interior-C2 inverse already
constructed on the physical domain.  This does not assert a C2 Schauder bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_physical_complete_C0_inverse_two
    {V : Set E} [CompactSpace (closure V)]
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (L : F ≃ₗᵢ[ℝ] E) (a b : Fin 2 → E)
    (hLa : ∀ i, L (realDirections i)=a i) (hLb : ∀ i, L (imagDirections i)=b i)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure V, (complexHessian a b w x).PosDef)
    (hwb : ∀ x ∈ frontier V, w x=0)
    {v ρ : E → ℝ} (hv : ContDiffOn ℝ 4 v V)
    (hvC : ContinuousOn v (closure V)) (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hvd : ∀ x ∈ V, (complexHessian a b v x).det=(ρ x : ℂ))
    (hρ : ContDiff ℝ 1 ρ) (hρlo : ∀ x ∈ V, 1 ≤ ρ x)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hvM : ∀ x ∈ closure V, -v x ≤ M)
    (A : EllipticCoeff (2+2) (L ⁻¹' V))
    (hA : ∀ x ∈ L ⁻¹' V, A.a x=c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x) :
    ∃ T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ), ‖T‖ ≤ M/2 ∧
      (∀ g : E → ℝ, ContinuousOn g (closure V) → ∃ H : E → ℝ,
        Continuous H ∧ MemH01 (fun y => H (L y)) (L ⁻¹' V) ∧
        ActualScalarWeakEquationTwo A (fun y => -(c⁻¹*ρ (L y)*g (L y)))
          (fun y => H (L y)) ∧
        (∀ x ∈ frontier V, H x=0) ∧
        ∀ hg : ContinuousOn g (closure V), ∀ x : closure V,
          T ⟨fun y => g y,hg.domRestrict⟩ x=H x) ∧
      ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
        Continuous h ∧ ContDiffOn ℝ 2 h V ∧
        (∀ x ∈ frontier V, h x=0) ∧
        (∀ x ∈ V, linearizedCMAOperatorTwo a b v h x=g x) ∧
        MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
        ActualScalarWeakEquationTwo A (fun y => -(c⁻¹*ρ (L y)*g (L y)))
          (fun y => h (L y)) ∧
        ∀ x : closure V,
          T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
  obtain ⟨T,hT,hzero,hclassical⟩ := actual_physical_C0_inverse_two
    hV hK L a b hLa hLb hw hwp hwb hv hvC hvb hvp hvd hρ hρlo hc hM hvM A hA
  refine ⟨T,hT,?_,hclassical⟩
  intro g hg
  let d : F → ℝ := fun y => c⁻¹*ρ (L y)
  have hd : ContinuousOn d (closure (L ⁻¹' V)) :=
    (continuous_const.mul (hρ.continuous.comp L.continuous)).continuousOn
  have hd0 : ∀ y ∈ L ⁻¹' V, 0 ≤ d y := by
    intro y hy
    exact mul_nonneg (inv_nonneg.mpr hc.le) ((by norm_num : (0 : ℝ) ≤ 1).trans (hρlo (L y) hy))
  have hcweak : ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
      Continuous h ∧ MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
      ActualScalarWeakEquationTwo A (fun y => -(d y*g (L y))) (fun y => h (L y)) ∧
      ∀ x : closure V, T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
    intro g hg
    obtain ⟨h,hhC,_,_,_,hh0,hhw,hhT⟩ := hclassical g hg
    exact ⟨h,hhC,hh0,hhw,hhT⟩
  obtain ⟨H,hHC,hH0,hHw,hHb,hHT⟩ :=
    actual_continuous_physical_load_weak_response_two hV hK L A hd hd0 T hzero hcweak hg
  exact ⟨H,hHC,hH0,hHw,hHb,fun _ => hHT⟩

end PowerConvexity
