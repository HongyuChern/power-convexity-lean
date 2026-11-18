import PowerConvexity.Calculus.ClassicalDirichletTwo
import PowerConvexity.Calculus.PowerBoundaryDecayTwo

/-! # Actual C0 stability under boundary changes on the strict classical branch

The comparison takes place on the physical domain. No pullback by a general
homeomorphism is asserted to preserve the complex Monge-Ampere operator.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem classical_boundary_C0_stability_two {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E)
    (hab : Orthonormal ℝ (Sum.elim a b)) {u v : E → ℝ} {δ : ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hAv : ∀ x ∈ U, (complexHessian a b v x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (complexHessian a b v x).det)
    (hb : ∀ x ∈ frontier U, |u x-v x| ≤ δ) :
    ∀ x ∈ closure U, |u x-v x| ≤ δ := by
  have huv := classical_comparison_two hU hK a b hab huc (hvc.add continuousOn_const)
    hu (hv.add contDiffOn_const) hAu
    (v := fun y => v y+δ)
    (fun x hx => by rw [complexHessian_add_const,hdet x hx])
    (fun x hx => by have hh := (abs_le.mp (hb x hx)).2; linarith)
  have hvu := classical_comparison_two hU hK a b hab hvc (huc.add continuousOn_const)
    hv (hu.add contDiffOn_const) hAv
    (v := fun y => u y+δ)
    (fun x hx => by rw [complexHessian_add_const,hdet x hx])
    (fun x hx => by have hh := (abs_le.mp (hb x hx)).1; linarith)
  intro x hx
  rw [abs_le]
  constructor <;> linarith [huv x hx,hvu x hx]

theorem classical_overlap_C0_stability_two {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u v : E → ℝ} {δ : ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure V))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v V)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hAv : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hdet : ∀ x ∈ U ∩ V, (complexHessian a b u x).det = (complexHessian a b v x).det)
    (hbu : ∀ x ∈ frontier U, u x = 0) (hbv : ∀ x ∈ frontier V, v x = 0)
    (hcollarU : ∀ x ∈ frontier U ∩ closure V, |v x| ≤ δ)
    (hcollarV : ∀ x ∈ closure U ∩ frontier V, |u x| ≤ δ) :
    ∀ x ∈ closure (U ∩ V), |u x-v x| ≤ δ := by
  have hsubU : closure (U ∩ V) ⊆ closure U := closure_mono inter_subset_left
  have hsubV : closure (U ∩ V) ⊆ closure V := closure_mono inter_subset_right
  apply classical_boundary_C0_stability_two (hU.inter hV)
    (hK.of_isClosed_subset isClosed_closure hsubU) a b hab
    (huc.mono hsubU) (hvc.mono hsubV) (hu.mono inter_subset_left) (hv.mono inter_subset_right)
    (fun x hx => hAu x hx.1) (fun x hx => hAv x hx.2) hdet
  intro x hx
  rcases frontier_inter_subset U V hx with h | h
  · rw [hbu x h.1,zero_sub,abs_neg]
    exact hcollarU x h
  · rw [hbv x h.2,sub_zero]
    exact hcollarV x h

end PowerConvexity
