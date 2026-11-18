import PowerConvexity.Calculus.SpectralHessianPositivityTwo

/-! # Nonnegative lowest root and the actual real Hessian -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem realHessian_nonneg_of_basis_block {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (hH : (realBlockHessian (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosSemidef)
    (v : E) : 0 ≤ realHessian u x v v := by
  let z : ι ⊕ ι → ℝ := fun i => e.repr v i
  have hp := hH.dotProduct_mulVec_nonneg z
  rw [star_trivial, ← realHessian_sum_directions_quadratic hu] at hp
  have he : (∑ i, z i • Sum.elim (fun i => e (.inl i)) (fun i => e (.inr i)) i) = v := by
    convert e.sum_repr v using 1
    apply Finset.sum_congr rfl
    intro i _
    cases i <;> rfl
  simpa only [he] using hp

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (hA : (complexHessian e (fun j => Complex.I • e j) u x).PosDef) :
    0 ≤ modifiedSigmaTwo e (fun j => Complex.I • e j) u x ↔
      ∀ v : E, 0 ≤ realHessian (powerTransform u) x v v := by
  have hM := schur_posSemidef_iff_lower_nonneg
    (modifiedA_posDef e (fun j => Complex.I • e j) hx hA)
    (modifiedB_transpose hu e (fun j => Complex.I • e j))
  have hB := realHessian_power_posSemidef_iff_modifiedSchur hu hx e (fun j => Complex.I • e j) hA
  constructor
  · intro hs v
    apply realHessian_nonneg_of_basis_block (powerTransform_contDiffAt hu hx) (complexRealBasis e) ?_ v
    simpa only [complexRealBasis_inl,complexRealBasis_inr] using hB.mpr (hM.mpr hs)
  · intro hQ
    apply hM.mp
    apply hB.mp
    exact realBlockHessian_posSemidef_of_quadratic_nonneg (powerTransform_contDiffAt hu hx) _ _ hQ

end PowerConvexity
