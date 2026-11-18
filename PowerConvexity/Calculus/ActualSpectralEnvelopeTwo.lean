import PowerConvexity.Calculus.ActualTouchPrincipleTwo
import PowerConvexity.Calculus.SpectralEnvelopeContact

/-! # Compact actual solution envelopes: branch PDE hypotheses discharged

Each touching branch has its own locally bounded PDE coefficient. No uniform
viscosity supersolution assertion for the envelope is used.
-/
set_option autoImplicit false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Nontrivial E]
variable {P : Type*} [TopologicalSpace P]

theorem actual_modifiedSigmaTwo_envelope_positive (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {S : Set P} (hS : IsCompact S) (hne : S.Nonempty) {u : P → E → ℝ}
    (hu : ∀ p ∈ S, ContDiffOn ℝ 4 (u p) U)
    (ρ : P → ℂ) (hρ : ∀ p ∈ S, ρ p ≠ 0)
    (hdet : ∀ p ∈ S, ∀ y ∈ U, (complexHessian a b (u p) y).det = ρ p)
    (hneg : ∀ p ∈ S, ∀ y ∈ U, u p y < 0)
    (hpos : ∀ p ∈ S, ∀ y ∈ U, (complexHessian a b (u p) y).PosDef)
    (hF : ContinuousOn (fun z : E × P => modifiedSigmaTwo a b (u z.2) z.1) (U ×ˢ S))
    (hnonneg : ∀ y ∈ U, 0 ≤ compactLowerEnvelope S
      (fun y p => modifiedSigmaTwo a b (u p) y) y)
    (hsep : ∀ x ∈ U, ∀ p ∈ S,
      modifiedSigmaTwo a b (u p) x = compactLowerEnvelope S
        (fun y q => modifiedSigmaTwo a b (u q) y) x →
      0 < eigenDiscriminantTwo (modifiedK a b (u p) x))
    (hanchor : ∃ x ∈ U, 0 < compactLowerEnvelope S
      (fun y p => modifiedSigmaTwo a b (u p) y) x) :
    ∀ x ∈ U, 0 < compactLowerEnvelope S (fun y p => modifiedSigmaTwo a b (u p) y) x := by
  apply modifiedSigmaTwo_envelope_positive a b e he hU hconn hS hne hu hneg hpos hF hnonneg hsep ?_ hanchor
  intro p hp x hx _ hgap
  apply modifiedSigmaTwo_eventually_gradient_estimate a b hU (hu p hp) (hρ p hp)
    (hdet p hp) (hneg p hp) (hpos p hp) ?_ hx hgap
  intro y hy
  exact (hnonneg y hy).trans (compactLowerEnvelope_le_on hS hne hF hy hp)

end PowerConvexity
