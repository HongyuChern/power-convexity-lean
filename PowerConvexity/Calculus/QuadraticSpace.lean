import PowerConvexity.Calculus.QuadraticTaylor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Finiteness.Prod

/-! # The finite-dimensional space of actual quadratic functions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (E → ℝ) where
  carrier := {q | IsQuadraticPolynomial q}
  zero_mem' := by
    refine ⟨0,0,0,?_,?_⟩ <;> simp
  add_mem' := IsQuadraticPolynomial_add
  smul_mem' r q hq := IsQuadraticPolynomial_const_mul hq r

/-- Fix the normed-space topology of the iterated continuous-linear-map
space before using its purely algebraic finite-dimensional structure. -/
@[reducible]
def quadraticJetSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ × ((E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ))

noncomputable def quadraticJetMapAt (x : E) :
    quadraticSubmodule E →ₗ[ℝ] quadraticJetSpace E where
  toFun q := (q.val x, fderiv ℝ q.val x, realHessian q.val x)
  map_add' q h := by
    have hq := (IsQuadraticPolynomial_contDiff q.property 2).contDiffAt (x := x)
    have hh := (IsQuadraticPolynomial_contDiff h.property 2).contDiffAt (x := x)
    change (q.val x+h.val x, fderiv ℝ (fun y => q.val y+h.val y) x,
        realHessian (fun y => q.val y+h.val y) x) =
      (q.val x+h.val x, fderiv ℝ q.val x+fderiv ℝ h.val x,
        realHessian q.val x+realHessian h.val x)
    rw [fderiv_fun_add (hq.differentiableAt (by norm_num))
      (hh.differentiableAt (by norm_num)),realHessian_add hq hh]
  map_smul' r q := by
    change (r*q.val x, fderiv ℝ (r • q.val) x,realHessian (fun y => r*q.val y) x) =
      (r*q.val x,r • fderiv ℝ q.val x,r • realHessian q.val x)
    rw [fderiv_const_smul_field,realHessian_const_mul]
    rfl

noncomputable def quadraticJetMap :
    quadraticSubmodule E →ₗ[ℝ] quadraticJetSpace E :=
  quadraticJetMapAt 0

/-- The actual two-jet is injective on functions, so no coefficient quotient
or formal polynomial surrogate is needed. -/
theorem quadraticJetMap_injective : Function.Injective (quadraticJetMap (E := E)) := by
  intro q h he
  have h0 : q.val 0 = h.val 0 := congrArg Prod.fst he
  have h1 : fderiv ℝ q.val 0 = fderiv ℝ h.val 0 := congrArg (fun z => z.2.1) he
  have h2 : realHessian q.val 0 = realHessian h.val 0 := congrArg (fun z => z.2.2) he
  apply Subtype.ext
  funext y
  rw [quadratic_exact_Taylor q.property 0 y,quadratic_exact_Taylor h.property 0 y,h0,h1,h2]

theorem quadraticSubmodule_finiteDimensional [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (quadraticSubmodule E) := by
  letI : AddCommGroup (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup
  letI : Module ℝ (quadraticJetSpace E) :=
    (inferInstance : NormedSpace ℝ (quadraticJetSpace E)).toModule
  letI : FiniteDimensional ℝ (quadraticJetSpace E) := by
    unfold quadraticJetSpace
    infer_instance
  exact FiniteDimensional.of_injective (quadraticJetMap (E := E))
    (quadraticJetMap_injective (E := E))

theorem IsPluriharmonicQuadratic_add {ι : Type*} {a b : ι → E} {q h : E → ℝ}
    (hq : IsPluriharmonicQuadratic a b q) (hh : IsPluriharmonicQuadratic a b h) :
    IsPluriharmonicQuadratic a b (q+h) := by
  refine ⟨IsQuadraticPolynomial_add hq.1 hh.1,?_⟩
  intro x
  change complexHessian a b (fun y => q y+h y) x = 0
  rw [complexHessian_add_at (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt
    (IsQuadraticPolynomial_contDiff hh.1 2).contDiffAt,hq.2 x,hh.2 x,zero_add]

def pluriharmonicQuadraticSubmodule {ι : Type*} (a b : ι → E) :
    Submodule ℝ (quadraticSubmodule E) where
  carrier := {q | ∀ x, complexHessian a b q.val x = 0}
  zero_mem' := by
    intro x
    change complexHessian a b (fun _ : E => 0) x = 0
    ext i j
    rw [complexHessian_real_entry contDiffAt_const]
    simp [realHessian]
  add_mem' := by
    intro q h hq hh
    exact (IsPluriharmonicQuadratic_add ⟨q.property,hq⟩ ⟨h.property,hh⟩).2
  smul_mem' := by
    intro r q hq
    exact (IsPluriharmonicQuadratic_const_mul ⟨q.property,hq⟩ r).2

theorem pluriharmonicQuadraticSubmodule_finiteDimensional [FiniteDimensional ℝ E]
    {ι : Type*} (a b : ι → E) : FiniteDimensional ℝ (pluriharmonicQuadraticSubmodule a b) := by
  letI := quadraticSubmodule_finiteDimensional (E := E)
  infer_instance

end PowerConvexity
