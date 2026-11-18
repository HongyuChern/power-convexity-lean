import PowerConvexity.Calculus.ActualClassicalResponseCompletionTwo
import PowerConvexity.Calculus.ActualPhysicalLinearizedDirichletTwo

/-! # The actual cofactor inverse on the complete C0 load space

For C1 loads the extended C0 operator is identified with the actual weak
Dirichlet solution, its classical C2 representative and its genuine zero
boundary.  For all continuous loads the result is a bounded C0 response with
zero boundary.  No closure-C2 regularity is inferred from the C0 norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_physical_C0_inverse_two
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
      (∀ f : C(closure V, ℝ), ∀ x, ∀ hx : x ∈ frontier V,
        T f ⟨x,frontier_subset_closure hx⟩=0) ∧
      ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
        Continuous h ∧ ContDiffOn ℝ 2 h V ∧
        (∀ x ∈ frontier V, h x=0) ∧
        (∀ x ∈ V, linearizedCMAOperatorTwo a b v h x=g x) ∧
        MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
        ActualScalarWeakEquationTwo A (fun y => -(c⁻¹*ρ (L y)*g (L y)))
          (fun y => h (L y)) ∧
        ∀ x : closure V,
          T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
  have hactual := actual_physical_linearized_zero_boundary_dirichlet_two
    hV hK L a b hLa hLb hw hwp hwb hv hvC hvb hvp hvd hρ hρlo hc A hA
  have hsolve : ∀ g : E → ℝ, ContDiff ℝ 1 g →
      ∃ h : E → ℝ, ClassicalLinearizedZeroDataTwo a b v V g h := by
    intro g hg
    obtain ⟨h,hhC,hh2,hhb,hhPDE,_⟩ := hactual g hg
    exact ⟨h,hhC.continuousOn,hh2,hhb,hhPDE⟩
  obtain ⟨R,hRn,hR⟩ := actual_classical_bounded_C0_response_two a b v
    hV hK hvC (hv.of_le (by norm_num)) hvb hvp hM hvM hsolve
  obtain ⟨T,hTn,hT,_⟩ := actual_classical_C0_response_extension_two R
  refine ⟨T,hTn.trans hRn,?_,?_⟩
  · intro f x hx
    exact actual_classical_C0_extension_zero_boundary_two hR hT f hx
  · intro g hg
    obtain ⟨h,hhC,hh2,hhb,hhPDE,hh0,hhweak,_⟩ := hactual g hg
    refine ⟨h,hhC,hh2,hhb,hhPDE,hh0,hhweak,?_⟩
    let f : classicalC1LoadClosureTwo V :=
      ⟨⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩,
        ⟨g,hg,fun _ => rfl⟩⟩
    have hhdata : ClassicalLinearizedZeroDataTwo a b v V g h :=
      ⟨hhC.continuousOn,hh2,hhb,hhPDE⟩
    have he := hR.eq_classical hV hK hvC (hv.of_le (by norm_num)) hvb hvp f
      (fun _ => rfl) hhdata
    intro x
    exact congrArg (fun k : C(closure V, ℝ) => k x) (hT f) |>.trans (he x)

end PowerConvexity
