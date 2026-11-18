import PowerConvexity.Calculus.ActualHolderDeterminantMapTwo
import CHS.Algebra.PositiveCone

/-! # The actual Holder complex Hessian and its open positive branch

Every field value is the actual closure Hessian of the same complete C2 jet.
The field is jointly continuous in the jet and the closed-domain point.
Its Hermitian symmetry follows from actual interior second derivatives and
closure continuity. Compactness then preserves strict positivity uniformly
on the entire closure under a sufficiently small change of the jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (U : Set E) [CompactSpace (closure U)]
local notation "Hess" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

def actualHolderComplexFieldTwo (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha) (x : closure U) : Mat :=
  actualDirectedComplexHessianFormTwo a b
    (actualHolderLoadSpaceTwo_value (closure U) Hess alpha
      (actualHolderC2JetSpaceTwo_hessian U alpha p) x)

theorem actualHolderComplexFieldTwo_continuous (alpha : ℝ) (a b : Fin 2 → E) :
    Continuous (fun p : actualHolderC2JetSpaceTwo U alpha × closure U =>
      actualHolderComplexFieldTwo U alpha a b p.1 p.2) := by
  let H := (actualHolderLoadSpaceTwo_value (closure U) Hess alpha).comp
    (actualHolderC2JetSpaceTwo_hessian U alpha)
  exact (actualDirectedComplexHessianFormTwo a b).continuous.comp
    (continuous_eval.comp ((H.continuous.comp continuous_fst).prodMk continuous_snd))

theorem actualHolderComplexFieldTwo_eq_actual (hU : IsOpen U) (alpha : ℝ)
    (a b : Fin 2 → E) (p : actualHolderC2JetSpaceTwo U alpha) {x : E} (hx : x ∈ U) :
    actualHolderComplexFieldTwo U alpha a b p ⟨x,subset_closure hx⟩ =
      complexHessian a b (actualClosureExtensionTwo U p.1.1) x := by
  obtain ⟨hp,J,_,hJ⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have he : actualHolderLoadSpaceTwo_value (closure U) Hess alpha
      (actualHolderC2JetSpaceTwo_hessian U alpha p) ⟨x,subset_closure hx⟩ =
      realHessian (actualClosureExtensionTwo U p.1.1) x := by
    have h := J.hessian_eq hx
    rw [hJ,actualClosureExtensionTwo_apply U _ (subset_closure hx)] at h
    exact h
  rw [actualHolderComplexFieldTwo,he,
    actualDirectedComplexHessianFormTwo_eq a b (hp.contDiffAt (hU.mem_nhds hx))]

theorem actualHolderComplexFieldTwo_isHermitian (hU : IsOpen U) (alpha : ℝ)
    (a b : Fin 2 → E) (p : actualHolderC2JetSpaceTwo U alpha) (x : closure U) :
    (actualHolderComplexFieldTwo U alpha a b p x).IsHermitian := by
  obtain ⟨hp,J,_,hJ⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have he : EqOn (fun y => (J.complexField a b y).conjTranspose) (J.complexField a b) U := by
    intro y hy
    change (J.complexField a b y).conjTranspose=J.complexField a b y
    rw [closure_complexField_eq_interior J hy (hp.contDiffAt (hU.mem_nhds hy)) a b]
    exact (complexHessian_isHermitian (hp.contDiffAt (hU.mem_nhds hy)) a b).eq
  have hc := J.continuousOn_complexField a b
  have hct : ContinuousOn (fun y => (J.complexField a b y).conjTranspose) (closure U) := by
    fun_prop
  have hb := he.of_subset_closure hct hc subset_closure (Subset.rfl : closure U ⊆ closure U) x.property
  change (actualHolderComplexFieldTwo U alpha a b p x).conjTranspose=
    actualHolderComplexFieldTwo U alpha a b p x
  have heq : actualHolderComplexFieldTwo U alpha a b p x=J.complexField a b x := by
    rw [ClosureC2Jet.complexField,hJ,actualClosureExtensionTwo_apply U _ x.property]
    rfl
  rwa [heq]

theorem actualHolderComplexFieldTwo_posDef_nhds (hU : IsOpen U) (alpha : ℝ)
    (a b : Fin 2 → E) (p : actualHolderC2JetSpaceTwo U alpha)
    (hp : ∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) :
    ∀ᶠ q in 𝓝 p, ∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b q x).PosDef := by
  have ho : IsOpen {z : actualHolderC2JetSpaceTwo U alpha × closure U |
      (actualHolderComplexFieldTwo U alpha a b z.1 z.2).PosDef} :=
    CHS.Algebra.isOpen_posDef_preimage (actualHolderComplexFieldTwo_continuous U alpha a b)
      (fun z => actualHolderComplexFieldTwo_isHermitian U hU alpha a b z.1 z.2)
  have hev : ∀ᶠ q : actualHolderC2JetSpaceTwo U alpha in 𝓝 p,
      ∀ x ∈ (univ : Set (closure U)), (actualHolderComplexFieldTwo U alpha a b q x).PosDef :=
    (isCompact_univ : IsCompact (univ : Set (closure U))).eventually_forall_of_forall_eventually
      (x₀ := p) (P := fun q x => (actualHolderComplexFieldTwo U alpha a b q x).PosDef)
      (fun x _ => ho.mem_nhds (hp x))
  simpa only [mem_univ,true_implies] using hev

end PowerConvexity
