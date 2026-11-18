import PowerConvexity.Analysis.ActualCofactorRawC0InverseTwo
import PowerConvexity.Analysis.ActualHolderWeakResponseDataTwo

/-! # The actual cofactor problem supplies the complete Holder-response data

Only the actual cofactor Holder bound remains explicit. The full C0
operator, every weak solution, qualitative C1 coefficient regularity,
divergence identity and true boundary trace are all constructed from the
actual classical background. The constant source weight corresponds to
the raw determinant derivative, with no missing density factor.
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

theorem actual_cofactor_holder_weak_response_data_two
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
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff v x)
    {alpha Ka : ℝ}
    (hAH : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha) :
    ∃ D : ActualHolderWeakResponseDataTwo U alpha Ka 0 c⁻¹,
      D.coeff=A ∧ D.weight=(fun _ => c⁻¹) ∧ ‖D.operator‖ ≤ M/2 := by
  obtain ⟨T,hT,hweak⟩ := actual_cofactor_complete_raw_C0_dirichlet_two
    hU hK hw hwp hwb hv hvC hvb hvp hvd hρ hρlo hc hM hvM A hA
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hv hvp hA
  have hpos : ∀ x ∈ U, (A.a x).PosDef := by
    intro x hx
    rw [hA x hx]
    exact (complexCofactorCoeff_posDef (hvp x hx)).smul (inv_pos.mpr hc)
  let D : ActualHolderWeakResponseDataTwo U alpha Ka 0 c⁻¹ := {
    coeff := A
    positive := hpos
    regular := hreg
    divergence := hdiv
    holder := hAH
    weight := fun _ => c⁻¹
    weight_continuous := continuousOn_const
    weight_bound := fun _ _ => by rw [abs_of_pos (inv_pos.mpr hc)]
    weight_holder := fun _ _ _ _ => by simp only [sub_self,abs_zero,zero_mul]; exact le_rfl
    operator := T
    weak := by
      intro g
      obtain ⟨H,hHC,hH0,hHw,hHb,hHT⟩ := hweak g
      exact ⟨H,hHw,hHT⟩
    zero := by
      intro g x hx
      obtain ⟨H,hHC,hH0,hHw,hHb,hHT⟩ := hweak g
      exact (hHT ⟨x,frontier_subset_closure hx⟩).trans (hHb x hx)
  }
  exact ⟨D,rfl,rfl,hT⟩

end PowerConvexity
