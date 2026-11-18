import PowerConvexity.Calculus.ComplexGradientMinimum
import PowerConvexity.Analysis.EnvelopeOn

/-!
# A lower envelope inherits local zero propagation from its touching branches

No common gradient constant for the family is assumed or asserted.  The
branch chosen at a contact point supplies its own local coefficient and
strictly psh potential.  The envelope itself need only be continuous.
-/

set_option autoImplicit false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Nontrivial E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem strictPsh_upper_contact_zero (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U V : Set E} (hV : IsOpen V) (hVU : V ⊆ U)
    {w f u : E → ℝ} (hnonneg : ∀ y ∈ U, 0 ≤ w y)
    (hupper : ∀ y ∈ V, w y ≤ f y) (hf : ContDiffOn ℝ 2 f V)
    (hu : ContDiffOn ℝ 4 u V) (hpos : ∀ y ∈ V, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ V) (hwx : w x = 0) (hcontact : f x = w x)
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      complexLinearized a b u f y ≤ c * (f y + ‖fderiv ℝ f y‖)) :
    ∀ᶠ y in 𝓝 x, w y = 0 := by
  have hf0 : f x = 0 := hcontact.trans hwx
  have hfnonneg : ∀ y ∈ V, 0 ≤ f y :=
    fun y hy => (hnonneg y (hVU hy)).trans (hupper y hy)
  have hz := strictPsh_gradient_local_zero a b e he hV hu hpos hf hfnonneg hx hf0 hest
  filter_upwards [hV.mem_nhds hx, hz] with y hy hy0
  exact le_antisymm (hy0 ▸ hupper y hy) (hnonneg y (hVU hy))

/-- Smoothness and the PDE are required only on a neighborhood of each zero
contact.  In particular a branch may develop a multiple eigenvalue elsewhere. -/
theorem lowerEnvelope_positive_of_local_branches (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {w : E → ℝ} (hw : ContinuousOn w U) (hnonneg : ∀ y ∈ U, 0 ≤ w y)
    (hbranches : ∀ x ∈ U, w x = 0 →
      ∃ (V : Set E) (f u : E → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ContDiffOn ℝ 2 f V ∧ ContDiffOn ℝ 4 u V ∧
        (∀ y ∈ V, (complexHessian a b u y).PosDef) ∧
        (∀ y ∈ V, w y ≤ f y) ∧ f x = w x ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
          complexLinearized a b u f y ≤ c * (f y + ‖fderiv ℝ f y‖))
    (hanchor : ∃ x ∈ U, 0 < w x) : ∀ x ∈ U, 0 < w x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn hw hnonneg ?_ hanchor
  intro x hx hx0
  obtain ⟨V, f, u, hV, hxV, hVU, hf, hu, hpos, hupper, hcontact, hest⟩ :=
    hbranches x hx hx0
  exact strictPsh_upper_contact_zero a b e he hV hVU hnonneg hupper hf hu hpos
    hxV hx0 hcontact hest

end PowerConvexity
