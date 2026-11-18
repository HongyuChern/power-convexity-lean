import PowerConvexity.Calculus.ActualClassicalResponseBoundedTwo
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The complete C0 load space and the extension of the actual response

Global C1 restrictions form a separating subalgebra and hence are dense on
the compact actual closure.  The bounded response therefore extends uniquely
to all continuous loads with no increase of its operator norm.  Only C1 loads
are identified here with classical C2 solutions; a continuous load is not
silently promoted to that regularity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The classical response is independent of the chosen global load extension,
weak representative, coefficient normalization, or existence witness. -/
theorem IsClassicalC0ResponseTwo.unique
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R Q : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    (hQ : IsClassicalC0ResponseTwo a b v Q) : R=Q := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  obtain ⟨g,h,hg,hfg,hh,hQh⟩ := hQ f
  exact (hR.eq_classical hV hK hvC hv2 hvb hvp f hfg hh x).trans (hQh x).symm

/-- The continuous-load extension inherits that same uniqueness. -/
theorem actual_classical_complete_C0_response_unique_two
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R Q : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    (hQ : IsClassicalC0ResponseTwo a b v Q)
    {T S : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ)}
    (hT : ∀ f : classicalC1LoadClosureTwo V, T f.1=R f)
    (hS : ∀ f : classicalC1LoadClosureTwo V, S f.1=Q f) : T=S := by
  have hRQ := hR.unique hV hK hvC hv2 hvb hvp hQ
  apply ContinuousLinearMap.ext
  intro f
  refine (classicalC1LoadClosureTwo_dense V).induction_on f
    (isClosed_eq T.continuous S.continuous) ?_
  intro k
  change T k.1=S k.1
  rw [hT,hS,hRQ]

/-- The extended response has the genuine zero boundary for every continuous
load.  This conclusion uses density in the actual C0 space. -/
theorem actual_classical_C0_extension_zero_boundary_two
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    {R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    {T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ)}
    (hT : ∀ f : classicalC1LoadClosureTwo V, T f.1=R f)
    (f : C(closure V, ℝ)) {x : E} (hx : x ∈ frontier V) :
    T f ⟨x,frontier_subset_closure hx⟩=0 := by
  let xK : closure V := ⟨x,frontier_subset_closure hx⟩
  change T f xK=0
  have hd := classicalC1LoadClosureTwo_dense V
  refine hd.induction_on f ?_ ?_
  · have heval : Continuous (fun w : C(closure V, ℝ) => w xK) := continuous_eval_const xK
    exact isClosed_eq (heval.comp T.continuous) continuous_const
  · intro k
    change T k.1 xK=0
    rw [hT k]
    obtain ⟨g,h,hg,hkg,hh,hRh⟩ := hR k
    rw [hRh]
    exact hh.2.2.1 x hx

end PowerConvexity
