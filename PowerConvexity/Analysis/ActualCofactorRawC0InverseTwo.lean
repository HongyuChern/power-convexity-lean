import PowerConvexity.Analysis.ActualCofactorCompleteC0InverseTwo
import PowerConvexity.Calculus.ActualClosureFunctionExtensionTwo
import Mathlib.Analysis.Normed.Operator.Mul

/-! # The actual complete C0 inverse for the raw determinant linearization

The previous response solves the density-normalized linearized operator.
Precomposing it with multiplication by the actual reciprocal density
removes that normalization. The exact source is now -c^(-1) g, including
for every continuous load, and the same norm bound and true zero trace are
preserved because the actual density is at least one.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_cofactor_complete_raw_C0_dirichlet_two
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
    ∃ T : C(closure U,ℝ) →L[ℝ] C(closure U,ℝ), ‖T‖ ≤ M/2 ∧
      ∀ g : C(closure U,ℝ), ∃ H : E → ℝ,
        Continuous H ∧ MemH01 H U ∧
        ActualScalarWeakEquationTwo A (fun x => -(c⁻¹*actualClosureExtensionTwo U g x)) H ∧
        (∀ x ∈ frontier U, H x=0) ∧ ∀ x : closure U, T g x=H x := by
  obtain ⟨T,hT,hweak,_⟩ := actual_cofactor_complete_C0_dirichlet_two
    hU hK hw hwp hwb hv hvC hvb hvp hvd hρ hρlo hc hM hvM A hA
  have hρC : ∀ x ∈ closure U, 1 ≤ ρ x := by
    intro x hx
    exact le_on_closure hρlo continuousOn_const hρ.continuous.continuousOn hx
  have hρpos : ∀ x ∈ closure U, 0 < ρ x := fun x hx => lt_of_lt_of_le zero_lt_one (hρC x hx)
  let R : C(closure U,ℝ) := ⟨fun x => (ρ x)⁻¹,
    ((hρ.continuous.continuousOn).inv₀ (fun x hx => (hρpos x hx).ne')).domRestrict⟩
  let L := ContinuousLinearMap.mul ℝ C(closure U,ℝ) R
  have hRn : ‖R‖ ≤ 1 := by
    apply (ContinuousMap.norm_le R zero_le_one).mpr
    intro x
    change |(ρ x)⁻¹| ≤ 1
    rw [abs_of_pos (inv_pos.mpr (hρpos x x.property))]
    exact inv_le_one_of_one_le₀ (hρC x x.property)
  have hLn : ‖L‖ ≤ 1 := (ContinuousLinearMap.opNorm_mul_apply_le ℝ C(closure U,ℝ) R).trans hRn
  refine ⟨T.comp L,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le T L).trans
      ((mul_le_of_le_one_right (norm_nonneg T) hLn).trans hT)
  · intro g
    let k := actualClosureExtensionTwo U (L g)
    have hkC := actualClosureExtensionTwo_continuousOn U (L g)
    obtain ⟨H,hHC,hH0,hHw,hHb,hHT⟩ := hweak k hkC
    have hk : (⟨fun x => k x,hkC.domRestrict⟩ : C(closure U,ℝ))=L g := by
      apply ContinuousMap.ext
      intro x
      exact actualClosureExtensionTwo_apply U _ x.property
    have hsource : (fun x => -(c⁻¹*ρ x*k x)) =ᵐ[volume.restrict U]
        (fun x => -(c⁻¹*actualClosureExtensionTwo U g x)) := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [show k x=L g ⟨x,subset_closure hx⟩ from actualClosureExtensionTwo_apply U _ (subset_closure hx),
        actualClosureExtensionTwo_apply U g (subset_closure hx)]
      change -(c⁻¹*ρ x*((ρ x)⁻¹*g ⟨x,subset_closure hx⟩))=-(c⁻¹*g ⟨x,subset_closure hx⟩)
      field_simp [(hρpos x (subset_closure hx)).ne']
    refine ⟨H,hHC,hH0,actual_scalar_weak_source_congr_ae_two hsource hHw,hHb,?_⟩
    intro x
    simpa only [ContinuousLinearMap.comp_apply,hk] using hHT x

end PowerConvexity
