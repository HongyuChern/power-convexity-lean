import PowerConvexity.Calculus.LinearizedDirichletC0Two
import PowerConvexity.Calculus.ActualClassicalLoadSpaceTwo

/-! # Actual linear response on the C0-normed classical load space

The load space consists of restrictions of global C1 functions to the actual
closed domain.  Equality in this space is equality of the actual load, not of
an arbitrarily chosen extension.  Classical uniqueness makes the response
well-defined; the maximum principle supplies its C0 operator norm.

This does not assert a closure C2 estimate or a Schauder inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Classical zero-boundary data for the same actual linearized operator. -/
def ClassicalLinearizedZeroDataTwo (a b : Fin 2 → E) (v : E → ℝ)
    (V : Set E) (g h : E → ℝ) : Prop :=
  ContinuousOn h (closure V) ∧ ContDiffOn ℝ 2 h V ∧
    (∀ x ∈ frontier V, h x=0) ∧
    (∀ x ∈ V, linearizedCMAOperatorTwo a b v h x=g x)

theorem linearizedCMAOperatorTwo_add_actual_two
    (a b : Fin 2 → E) (v : E → ℝ) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    linearizedCMAOperatorTwo a b v (fun y => f y+g y) x =
      linearizedCMAOperatorTwo a b v f x+linearizedCMAOperatorTwo a b v g x := by
  simp only [linearizedCMAOperatorTwo,realHessian_add hf hg,map_add]

theorem linearizedCMAOperatorTwo_smul_actual_two
    (a b : Fin 2 → E) (v : E → ℝ) (c : ℝ) (f : E → ℝ) (x : E) :
    linearizedCMAOperatorTwo a b v (fun y => c*f y) x =
      c*linearizedCMAOperatorTwo a b v f x := by
  simp only [linearizedCMAOperatorTwo,realHessian_const_mul,map_smul,smul_eq_mul]

theorem ClassicalLinearizedZeroDataTwo.add
    {a b : Fin 2 → E} {v : E → ℝ} {V : Set E} (hV : IsOpen V)
    {g₁ g₂ h₁ h₂ : E → ℝ}
    (h₁data : ClassicalLinearizedZeroDataTwo a b v V g₁ h₁)
    (h₂data : ClassicalLinearizedZeroDataTwo a b v V g₂ h₂) :
    ClassicalLinearizedZeroDataTwo a b v V (fun x => g₁ x+g₂ x)
      (fun x => h₁ x+h₂ x) := by
  refine ⟨h₁data.1.add h₂data.1,h₁data.2.1.add h₂data.2.1,?_,?_⟩
  · intro x hx
    change h₁ x+h₂ x=0
    rw [h₁data.2.2.1 x hx,h₂data.2.2.1 x hx,add_zero]
  · intro x hx
    rw [linearizedCMAOperatorTwo_add_actual_two a b v
      (h₁data.2.1.contDiffAt (hV.mem_nhds hx))
      (h₂data.2.1.contDiffAt (hV.mem_nhds hx)),h₁data.2.2.2 x hx,h₂data.2.2.2 x hx]

theorem ClassicalLinearizedZeroDataTwo.smul
    {a b : Fin 2 → E} {v : E → ℝ} {V : Set E} {g h : E → ℝ}
    (hd : ClassicalLinearizedZeroDataTwo a b v V g h) (c : ℝ) :
    ClassicalLinearizedZeroDataTwo a b v V (fun x => c*g x) (fun x => c*h x) := by
  refine ⟨continuousOn_const.mul hd.1,contDiffOn_const.mul hd.2.1,?_,?_⟩
  · intro x hx
    change c*h x=0
    rw [hd.2.2.1 x hx,mul_zero]
  · intro x hx
    rw [linearizedCMAOperatorTwo_smul_actual_two,hd.2.2.2 x hx]

theorem ClassicalLinearizedZeroDataTwo.eqOn_of_load_eq
    {a b : Fin 2 → E} {v : E → ℝ} {V : Set E}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {g₁ g₂ h₁ h₂ : E → ℝ}
    (h₁data : ClassicalLinearizedZeroDataTwo a b v V g₁ h₁)
    (h₂data : ClassicalLinearizedZeroDataTwo a b v V g₂ h₂)
    (hload : EqOn g₁ g₂ V) : EqOn h₁ h₂ (closure V) := by
  have hsub := h₁data.add hV (h₂data.smul (-1))
  have hz := linearizedCMAOperatorTwo_zero_kernel a b hV hK hvC hv2 hvb hvp
    hsub.1 hsub.2.1 hsub.2.2.1 (by
      intro x hx
      rw [hsub.2.2.2 x hx]
      change g₁ x+(-1)*g₂ x=0
      rw [hload hx]
      ring)
  intro x hx
  have hh := hz hx
  dsimp only at hh
  linarith

theorem ClassicalLinearizedZeroDataTwo.difference_bound
    {a b : Fin 2 → E} {v : E → ℝ} {V : Set E}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {g₁ g₂ h₁ h₂ : E → ℝ}
    (h₁data : ClassicalLinearizedZeroDataTwo a b v V g₁ h₁)
    (h₂data : ClassicalLinearizedZeroDataTwo a b v V g₂ h₂)
    {F : ℝ} (hload : ∀ x ∈ V, |g₁ x-g₂ x| ≤ F) :
    ∀ x ∈ closure V, |h₁ x-h₂ x| ≤ (F/2)*(-v x) := by
  have hsub := h₁data.add hV (h₂data.smul (-1))
  have hb := linearizedCMAOperatorTwo_abs_bound a b hV hK hvC hv2 hvb hvp
    hsub.1 hsub.2.1 hsub.2.2.1 (C := F) (by
      intro x hx
      rw [hsub.2.2.2 x hx]
      simpa only [neg_one_mul,sub_eq_add_neg] using hload x hx)
  simpa only [neg_one_mul,sub_eq_add_neg] using hb

end PowerConvexity
