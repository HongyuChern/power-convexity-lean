import PowerConvexity.Calculus.ActualClassicalResponseLinearTwo
import Mathlib.Topology.ContinuousMap.Compact

/-! # A bounded classical response with the actual C0 load norm

No completeness of the C1-restriction load subspace is assumed.  The map
constructed here takes values in the complete C0 space.  The later dense
extension is needed before one can use all continuous loads.
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

/-- The load and output are equal on the actual closure to the stated global
classical representatives.  This property does not require a C2 extension
across the boundary. -/
def IsClassicalC0ResponseTwo {V : Set E} [CompactSpace (closure V)]
    (a b : Fin 2 → E) (v : E → ℝ)
    (R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)) : Prop :=
  ∀ f : classicalC1LoadClosureTwo V, ∃ g h : E → ℝ,
    ContDiff ℝ 1 g ∧ (∀ x : closure V, f.1 x=g x) ∧
    ClassicalLinearizedZeroDataTwo a b v V g h ∧
    ∀ x : closure V, R f x=h x

theorem actual_classical_bounded_C0_response_two
    {V : Set E} [CompactSpace (closure V)]
    (a b : Fin 2 → E) (v : E → ℝ)
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {B : ℝ} (hB : 0 ≤ B) (hvB : ∀ x ∈ closure V, -v x ≤ B)
    (hsolve : ∀ g : E → ℝ, ContDiff ℝ 1 g →
      ∃ h : E → ℝ, ClassicalLinearizedZeroDataTwo a b v V g h) :
    ∃ R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ),
      ‖R‖ ≤ B/2 ∧ IsClassicalC0ResponseTwo a b v R := by
  let S := classicalC1LoadClosureTwo V
  have hrep (f : S) : ∃ g : E → ℝ, ContDiff ℝ 1 g ∧
      ∀ x : closure V, f.1 x=g x := f.property
  choose g hg hfg using hrep
  choose h hh using fun f : S => hsolve (g f) (hg f)
  let T : S → C(closure V, ℝ) := fun f =>
    ⟨fun x => h f x,(hh f).1.domRestrict⟩
  have hTadd (f k : S) : T (f+k)=T f+T k := by
    apply ContinuousMap.ext
    intro x
    change h (f+k) x=h f x+h k x
    apply (hh (f+k)).eqOn_of_load_eq hV hK hvC hv2 hvb hvp
      ((hh f).add hV (hh k)) _ x.property
    intro y hy
    have hfk := hfg (f+k) ⟨y,subset_closure hy⟩
    have hf := hfg f ⟨y,subset_closure hy⟩
    have hk := hfg k ⟨y,subset_closure hy⟩
    change f.1 ⟨y,subset_closure hy⟩+k.1 ⟨y,subset_closure hy⟩=g (f+k) y at hfk
    rw [hf,hk] at hfk
    exact hfk.symm
  have hTsmul (c : ℝ) (f : S) : T (c • f)=c • T f := by
    apply ContinuousMap.ext
    intro x
    change h (c • f) x=c*h f x
    apply (hh (c • f)).eqOn_of_load_eq hV hK hvC hv2 hvb hvp
      ((hh f).smul c) _ x.property
    intro y hy
    have hcf := hfg (c • f) ⟨y,subset_closure hy⟩
    have hf := hfg f ⟨y,subset_closure hy⟩
    change c*f.1 ⟨y,subset_closure hy⟩=g (c • f) y at hcf
    rw [hf] at hcf
    exact hcf.symm
  let L : S →ₗ[ℝ] C(closure V, ℝ) :=
    { toFun := T
      map_add' := hTadd
      map_smul' := hTsmul }
  have hbound (f : S) : ‖L f‖ ≤ (B/2)*‖f‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg hB (by norm_num))
      (norm_nonneg f))).mpr
    intro x
    change ‖h f x‖ ≤ (B/2)*‖f‖
    have hload : ∀ y ∈ V, |linearizedCMAOperatorTwo a b v (h f) y| ≤ ‖f‖ := by
      intro y hy
      rw [(hh f).2.2.2 y hy,← hfg f ⟨y,subset_closure hy⟩]
      simpa only [Real.norm_eq_abs,Submodule.norm_coe] using f.1.norm_coe_le_norm ⟨y,subset_closure hy⟩
    have hb := linearizedCMAOperatorTwo_abs_bound a b hV hK hvC hv2 hvb hvp
      (hh f).1 (hh f).2.1 (hh f).2.2.1 hload x x.property
    have hb' : (‖f‖/2)*(-v x) ≤ (‖f‖/2)*B :=
      mul_le_mul_of_nonneg_left (hvB x x.property)
        (div_nonneg (norm_nonneg f) (by norm_num))
    rw [Real.norm_eq_abs]
    calc
      |h f x| ≤ (‖f‖/2)*(-v x) := hb
      _ ≤ (‖f‖/2)*B := hb'
      _ = (B/2)*‖f‖ := by ring
  let R : S →L[ℝ] C(closure V, ℝ) := L.mkContinuous (B/2) hbound
  refine ⟨R,L.mkContinuous_norm_le (div_nonneg hB (by norm_num)) hbound,?_⟩
  intro f
  exact ⟨g f,h f,hg f,hfg f,hh f,fun _ => rfl⟩

/-- Any C1 representative gives the same classical response.  The result
therefore does not depend on the extension used in the source submodule. -/
theorem IsClassicalC0ResponseTwo.eq_classical
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    (f : classicalC1LoadClosureTwo V) {g h : E → ℝ}
    (hfg : ∀ x : closure V, f.1 x=g x)
    (hh : ClassicalLinearizedZeroDataTwo a b v V g h) :
    ∀ x : closure V, R f x=h x := by
  obtain ⟨g',h',hg',hf',hh',hRh⟩ := hR f
  have he : EqOn h' h (closure V) := hh'.eqOn_of_load_eq hV hK hvC hv2 hvb hvp hh
    (fun x hx => (hf' ⟨x,subset_closure hx⟩).symm.trans (hfg ⟨x,subset_closure hx⟩))
  intro x
  exact (hRh x).trans (he x.property)

end PowerConvexity
