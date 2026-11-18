import PowerConvexity.Calculus.MinimalEigenvalueContact
import PowerConvexity.Analysis.BranchContact

/-!
# Actual dimension-two spectral envelopes at contact

Compactness supplies an attaining parameter.  A positive spectral gap at that
parameter and the branch differential inequality imply local zero propagation.
Neither the gap nor the differential inequality is silently assumed proved.
-/

set_option autoImplicit false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Nontrivial E]
variable {P : Type*} [TopologicalSpace P]

theorem modifiedSigmaTwo_envelope_positive (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {S : Set P} (hS : IsCompact S) (hne : S.Nonempty) {u : P → E → ℝ}
    (hu : ∀ p ∈ S, ContDiffOn ℝ 4 (u p) U)
    (hneg : ∀ p ∈ S, ∀ y ∈ U, u p y < 0)
    (hpos : ∀ p ∈ S, ∀ y ∈ U, (complexHessian a b (u p) y).PosDef)
    (hF : ContinuousOn (fun z : E × P => modifiedSigmaTwo a b (u z.2) z.1) (U ×ˢ S))
    (hnonneg : ∀ y ∈ U, 0 ≤ compactLowerEnvelope S
      (fun y p => modifiedSigmaTwo a b (u p) y) y)
    (hsep : ∀ x ∈ U, ∀ p ∈ S,
      modifiedSigmaTwo a b (u p) x = compactLowerEnvelope S
        (fun y q => modifiedSigmaTwo a b (u q) y) x →
      0 < eigenDiscriminantTwo (modifiedK a b (u p) x))
    (hest : ∀ p ∈ S, ∀ x ∈ U, modifiedSigmaTwo a b (u p) x = 0 →
      0 < eigenDiscriminantTwo (modifiedK a b (u p) x) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
        complexLinearized a b (u p) (modifiedSigmaTwo a b (u p)) y ≤
          c * (modifiedSigmaTwo a b (u p) y + ‖fderiv ℝ (modifiedSigmaTwo a b (u p)) y‖))
    (hanchor : ∃ x ∈ U, 0 < compactLowerEnvelope S
      (fun y p => modifiedSigmaTwo a b (u p) y) x) :
    ∀ x ∈ U, 0 < compactLowerEnvelope S (fun y p => modifiedSigmaTwo a b (u p) y) x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn
    (compactLowerEnvelope_continuousOn hS hF) hnonneg ?_ hanchor
  intro x hx hx0
  obtain ⟨p, hp, heq, _⟩ := compactLowerEnvelope_attains_on
    (F := fun y p => modifiedSigmaTwo a b (u p) y) hS hne hF hx
  have hp0 : modifiedSigmaTwo a b (u p) x = 0 := heq.symm.trans hx0
  have hgap := hsep x hx p hp heq.symm
  have hupper (y : E) (hy : y ∈ U) := compactLowerEnvelope_le_on
    (F := fun y p => modifiedSigmaTwo a b (u p) y) hS hne hF hy hp
  have hbranchNonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b (u p) y :=
    fun y hy => (hnonneg y hy).trans (hupper y hy)
  have hz := modifiedSigmaTwo_local_zero_of_estimate a b e he hU (hu p hp)
    (hneg p hp) (hpos p hp) hbranchNonneg hx hp0 hgap (hest p hp x hx hp0 hgap)
  filter_upwards [hU.mem_nhds hx, hz] with y hy hy0
  exact le_antisymm (hy0 ▸ hupper y hy) (hnonneg y hy)

end PowerConvexity
