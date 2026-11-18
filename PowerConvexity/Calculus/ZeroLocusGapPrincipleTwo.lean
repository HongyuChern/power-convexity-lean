import PowerConvexity.Calculus.ActualTouchPrincipleTwo

/-! # The spectral gap is needed only on the zero locus

Positive points may have a repeated lowest root, as the centre of a ball does.
The proof uses continuity everywhere and the actual local estimate only at zeros.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Nontrivial E]

theorem modifiedSigmaTwo_positive_of_gap_on_zero_locus (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    (hgap : ∀ y ∈ U, modifiedSigmaTwo a b u y = 0 →
      0 < eigenDiscriminantTwo (modifiedK a b u y))
    (hanchor : ∃ x ∈ U, 0 < modifiedSigmaTwo a b u x) :
    ∀ x ∈ U, 0 < modifiedSigmaTwo a b u x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn
    (modifiedSigmaTwo_continuousOn a b hU hu hneg hpos) hnonneg ?_ hanchor
  intro x hx hx0
  exact modifiedSigmaTwo_actual_local_zero a b e he hU hu hρ hdet hneg hpos hnonneg hx hx0 (hgap x hx hx0)

end PowerConvexity
