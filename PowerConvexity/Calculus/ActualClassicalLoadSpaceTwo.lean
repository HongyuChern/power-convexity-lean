import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The actual C1 restriction load space and its C0 completion

The source consists of restrictions of global C1 functions, with the genuine
C0 norm on the compact closed domain.  It is a dense subspace, not asserted to
be complete.  A bounded linear map from this source into C0 has a unique
norm-preserving extension to all continuous loads.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Metric
open scoped ContDiff Topology RealInnerProductSpace NNReal
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual closed-domain loads which admit a global C1 representative. -/
def classicalC1LoadClosureTwo (V : Set E) : Submodule ℝ C(closure V, ℝ) where
  carrier := {f | ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ ∀ x : closure V, f x = g x}
  zero_mem' := ⟨fun _ => 0, contDiff_const, fun _ => rfl⟩
  add_mem' := by
    rintro f k ⟨g,hg,hfg⟩ ⟨l,hl,hkl⟩
    exact ⟨fun x => g x+l x, hg.add hl, fun x => by
      change f x+k x=g x+l x
      rw [hfg,hkl]⟩
  smul_mem' := by
    rintro c f ⟨g,hg,hfg⟩
    exact ⟨fun x => c*g x, contDiff_const.mul hg, fun x => by
      change c*f x=c*g x
      rw [hfg]⟩

/-- The same C1 restriction space is an algebra, so Stone-Weierstrass applies. -/
def classicalC1LoadClosureAlgebraTwo (V : Set E) : Subalgebra ℝ C(closure V, ℝ) where
  carrier := {f | ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ ∀ x : closure V, f x=g x}
  zero_mem' := ⟨fun _ => 0,contDiff_const,fun _ => rfl⟩
  one_mem' := ⟨fun _ => 1,contDiff_const,fun _ => rfl⟩
  add_mem' := by
    rintro f k ⟨g,hg,hfg⟩ ⟨l,hl,hkl⟩
    exact ⟨fun x => g x+l x,hg.add hl,fun x => by
      change f x+k x=g x+l x
      rw [hfg,hkl]⟩
  mul_mem' := by
    rintro f k ⟨g,hg,hfg⟩ ⟨l,hl,hkl⟩
    exact ⟨fun x => g x*l x,hg.mul hl,fun x => by
      change f x*k x=g x*l x
      rw [hfg,hkl]⟩
  algebraMap_mem' := fun c => ⟨fun _ => c,contDiff_const,fun _ => rfl⟩

theorem classicalC1LoadClosureAlgebraTwo_separates (V : Set E) :
    (classicalC1LoadClosureAlgebraTwo V).SeparatesPoints := by
  intro x y hxy
  let g : E → ℝ := fun z => inner ℝ z ((x : E)-(y : E))
  have hg : ContDiff ℝ 1 g := contDiff_id.inner ℝ contDiff_const
  let f : C(closure V, ℝ) := ⟨fun z => g z,hg.continuous.comp continuous_subtype_val⟩
  refine ⟨(f : closure V → ℝ),⟨f,⟨g,hg,fun _ => rfl⟩,rfl⟩,?_⟩
  intro he
  have hz : inner ℝ ((x : E)-(y : E)) ((x : E)-(y : E))=0 := by
    rw [inner_sub_left]
    change g x-g y=0
    exact sub_eq_zero.mpr he
  have hz' : (x : E)-(y : E)=0 := (inner_self_eq_zero.mp hz)
  exact hxy (Subtype.ext (sub_eq_zero.mp hz'))

theorem classicalC1LoadClosureTwo_dense
    (V : Set E) [CompactSpace (closure V)] :
    DenseRange (classicalC1LoadClosureTwo V).subtypeL := by
  have he := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (classicalC1LoadClosureAlgebraTwo V) (classicalC1LoadClosureAlgebraTwo_separates V)
  change Dense (Set.range (fun f : classicalC1LoadClosureTwo V => (f : C(closure V, ℝ))))
  have hr : Set.range (fun f : classicalC1LoadClosureTwo V => (f : C(closure V, ℝ))) =
      (classicalC1LoadClosureTwo V : Set C(closure V, ℝ)) := by
    ext f
    constructor
    · rintro ⟨k,rfl⟩
      exact k.property
    · intro hf
      exact ⟨⟨f,hf⟩,rfl⟩
  rw [hr,dense_iff_closure_eq]
  have hh := congrArg (fun A : Subalgebra ℝ C(closure V, ℝ) => (A : Set C(closure V, ℝ))) he
  rw [Subalgebra.topologicalClosure_coe,Algebra.coe_top] at hh
  have hset : (classicalC1LoadClosureTwo V : Set C(closure V, ℝ)) =
      (classicalC1LoadClosureAlgebraTwo V : Set C(closure V, ℝ)) := by rfl
  rw [hset]
  exact hh

theorem actual_classical_C0_response_extension_two
    {V : Set E} [CompactSpace (closure V)]
    (R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)) :
    ∃ T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ),
      ‖T‖ ≤ ‖R‖ ∧ (∀ f : classicalC1LoadClosureTwo V, T f.1=R f) ∧
      ∀ Q : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ),
        (∀ f : classicalC1LoadClosureTwo V, Q f.1=R f) → Q=T := by
  let S := classicalC1LoadClosureTwo V
  let e := S.subtypeL
  have hd : DenseRange e := classicalC1LoadClosureTwo_dense V
  have hi : IsUniformInducing e := isometry_subtype_coe.isUniformInducing
  let T := R.extend e
  have hT (f : S) : T f.1=R f := R.extend_eq hd hi f
  refine ⟨T,?_,hT,?_⟩
  · have hb : ∀ f : S, ‖f‖ ≤ (1 : ℝ≥0)*‖e f‖ := by intro f; simp [e]
    simpa only [NNReal.coe_one,one_mul] using R.opNorm_extend_le hd hb
  · intro Q hQ
    exact (R.extend_unique hd hi Q (ContinuousLinearMap.ext hQ)).symm


end PowerConvexity
