import PowerConvexity.Algebra.BoundaryMixedControlTwo
import PowerConvexity.Calculus.ConvexDefiningCurvature

/-! # The actual boundary normal diagonal from a genuine mixed-entry estimate

This is a reduction with an explicit mixed-entry hypothesis. No such estimate
is asserted to follow from the determinant equation alone.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem classicalDirichlet_boundary_normal_upper_of_mixed_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (htan : fderiv ℝ f x (b 1) = 0)
    {delta M : ℝ} (hd : 0 < delta)
    (hLevi : delta ≤ (J.complexField a b x 0 0).re)
    (hmixed : Complex.normSq (J.complexField a b x 0 1) ≤ M) :
    J.hessian x (a 1) (a 1) ≤ 4*(1+M)/delta := by
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hb a b hab hpsh hdet hx hf hfx hDf hdef
  have hbt : 0 ≤ J.hessian x (b 1) (b 1) := by
    rw [hH (b 1) (b 1) htan htan]
    exact mul_nonneg hlam.le
      (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef (b 1) htan)
  have hA := closure_complexField_posDef_of_constantDensity J hU hu a b one_ne_zero
    hdet hpsh x (frontier_subset_closure hx)
  have hAd := closure_complexField_constantDensity J hU hu a b 1 hdet x (frontier_subset_closure hx)
  have hn := hermitian_det_one_normal_diagonal_bound_two hA hAd hd hLevi hmixed
  have he : (J.complexField a b x 1 1).re =
      (J.hessian x (a 1) (a 1)+J.hessian x (b 1) (b 1))/4 := by
    simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.mul_re,Complex.mul_im]
    <;> ring
  calc
    J.hessian x (a 1) (a 1) ≤ 4*(J.complexField a b x 1 1).re := by rw [he]; linarith
    _ ≤ 4*((1+M)/delta) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = 4*(1+M)/delta := by ring

end PowerConvexity
