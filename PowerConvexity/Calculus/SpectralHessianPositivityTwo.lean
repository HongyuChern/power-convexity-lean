import PowerConvexity.Calculus.ComplexRealBasis
import PowerConvexity.Calculus.ScalarBasis
import PowerConvexity.Calculus.EigenvalueFieldTwo

/-! # Positive lowest modified root and the public strict convexity bridge

The Hessian criterion is equivalent to positive sigma in the strict psh branch.
The passage to StrictConvexOn is one-way; its false converse is never used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem modifiedSigmaTwo_pos_iff_powerHessian_pos
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (hA : (complexHessian e (fun j => Complex.I • e j) u x).PosDef) :
    0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x ↔
      ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  have hM := schur_posDef_iff_lower_pos
    (modifiedA_posDef e (fun j => Complex.I • e j) hx hA)
    (modifiedB_transpose hu e (fun j => Complex.I • e j))
  have hB := realHessian_power_posDef_iff_modifiedSchur hu hx e (fun j => Complex.I • e j) hA
  constructor
  · intro hs v hv
    apply realHessian_pos_of_basis_block (powerTransform_contDiffAt hu hx) (complexRealBasis e) ?_ v hv
    simpa only [complexRealBasis_inl,complexRealBasis_inr] using hB.mpr (hM.mpr hs)
  · intro hQ
    apply hM.mp
    apply hB.mp
    simpa only [complexRealBasis_inl,complexRealBasis_inr] using
      realBlockHessian_posDef_of_basis_quadratic (powerTransform_contDiffAt hu hx) (complexRealBasis e) hQ

theorem strictConvexOn_power_of_modifiedSigmaTwo
    (e : Module.Basis (Fin 2) ℂ E) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hneg : ∀ x ∈ U, u x < 0)
    (hA : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hσ : ∀ x ∈ U, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x) :
    StrictConvexOn ℝ U (powerTransform u) := by
  apply strictConvexOn_of_realHessian_pos hU hconv (powerTransform_contDiffOn hu hneg)
  intro x hx
  exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) (hA x hx)).mp (hσ x hx)

end PowerConvexity
