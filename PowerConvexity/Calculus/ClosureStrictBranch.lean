import PowerConvexity.Calculus.ModifiedSchur
import CHS.Calculus.ClosureJets

/-! # The strict classical complex Hessian branch extends to the closure

Only continuous extensions of the actual interior derivatives are used.
There is no ambient differentiability assumption at a Dirichlet boundary point.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem closure_complexField_eq_interior {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    J.complexField a b x = complexHessian a b u x := by
  ext i j
  rw [ClosureC2Jet.complexField,J.hessian_eq hx]
  exact (complexHessian_real_entry hu a b i j).symm

theorem closure_complexField_constantDensity {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (ρ : ℂ) (hdet : ∀ x ∈ U, (complexHessian a b u x).det = ρ) :
    ∀ x ∈ closure U, (J.complexField a b x).det = ρ := by
  have he : EqOn (fun x => (J.complexField a b x).det) (fun _ => ρ) U := by
    intro x hx
    change (J.complexField a b x).det = ρ
    rw [closure_complexField_eq_interior J hx (hu.contDiffAt (hU.mem_nhds hx)) a b]
    exact hdet x hx
  exact he.of_subset_closure
    (continuous_id.matrix_det.comp_continuousOn (J.continuousOn_complexField a b))
    continuousOn_const subset_closure Subset.rfl

theorem closure_complexField_posSemidef {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hpos : ∀ x ∈ U, (complexHessian a b u x).PosSemidef) :
    ∀ x ∈ closure U, (J.complexField a b x).PosSemidef := by
  intro x hx
  have hA := J.continuousOn_complexField a b
  have hH : (J.complexField a b x).IsHermitian := by
    have he : EqOn (fun y => (J.complexField a b y).conjTranspose) (J.complexField a b) U := by
      intro y hy
      change (J.complexField a b y).conjTranspose = J.complexField a b y
      rw [closure_complexField_eq_interior J hy (hu.contDiffAt (hU.mem_nhds hy)) a b]
      exact (hpos y hy).isHermitian
    have hc : ContinuousOn (fun y => (J.complexField a b y).conjTranspose) (closure U) := by fun_prop
    exact he.of_subset_closure hc hA subset_closure Subset.rfl hx
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro z
  have hle : ∀ y ∈ U, (0:ℂ) ≤ star z ⬝ᵥ (J.complexField a b y).mulVec z := by
    intro y hy
    rw [closure_complexField_eq_interior J hy (hu.contDiffAt (hU.mem_nhds hy)) a b]
    exact (hpos y hy).dotProduct_mulVec_nonneg z
  have hc : ContinuousOn (fun y => star z ⬝ᵥ (J.complexField a b y).mulVec z) (closure U) := by
    have hA := J.continuousOn_complexField a b
    simp only [dotProduct,Matrix.mulVec]
    fun_prop
  exact le_on_closure hle continuousOn_const hc hx

theorem closure_complexField_posDef_of_constantDensity {u : E → ℝ} {U : Set E}
    (J : ClosureC2Jet u U) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = ρ)
    (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef) :
    ∀ x ∈ closure U, (J.complexField a b x).PosDef := by
  intro x hx
  apply (closure_complexField_posSemidef J hU hu a b
    (fun y hy => (hpos y hy).posSemidef) x hx).posDef_iff_det_ne_zero.mpr
  rw [closure_complexField_constantDensity J hU hu a b ρ hdet x hx]
  exact hρ

end PowerConvexity
