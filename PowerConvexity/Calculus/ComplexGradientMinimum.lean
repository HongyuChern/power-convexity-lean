import PowerConvexity.Analysis.ContinuousEllipticity
import PowerConvexity.Calculus.MatrixInverse

/-!
# The actual strictly psh linearization and the gradient minimum principle

The complex contraction uses `W q p` and the actual order `dbar_q d_p`.
The real coefficient matrix includes the factor `1/4`.  Its local ellipticity
bounds follow from the actual complex Hessian being positive definite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology BigOperators ComplexOrder

namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def complexHessianContraction (a b : ι → E) (W : Matrix ι ι ℂ) :
    (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  matrixHessianContraction (Sum.elim a b) (realLinearizationMatrix W)

/-- The order and the factor of the actual Wirtinger operator are explicit. -/
theorem complexHessianContraction_pairing (a b : ι → E) (W : Matrix ι ι ℂ)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (∑ p, ∑ q, W q p * dz (a q) (-b q)
      (dz (a p) (b p) (fun y => (f y : ℂ))) x).re =
      complexHessianContraction a b W (realHessian f x) := by
  have hfc : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  simp_rw [dz_comm_at hfc (a _) (-b _) (a _) (b _)]
  calc
    _ = ∑ i, ∑ j, realLinearizationMatrix W i j * realBlockHessian a b f x i j :=
      realLinearizationMatrix_pairing hf a b W
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [realBlockHessian, realHessian_symm hf]

theorem complexHessianContraction_positive (a b : ι → E) {W : Matrix ι ι ℂ}
    (hW : W.PosDef) : HessianPositive (complexHessianContraction a b W) :=
  matrixHessianContraction_positive _ (realLinearizationMatrix_posDef hW).posSemidef

noncomputable def complexLinearized (a b : ι → E) (u f : E → ℝ) (x : E) : ℝ :=
  (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p * dz (a q) (-b q)
    (dz (a p) (b p) (fun y => (f y : ℂ))) x).re

theorem complexLinearized_eq_real (a b : ι → E) (u : E → ℝ)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    complexLinearized a b u f x =
      complexHessianContraction a b (complexHessian a b u x)⁻¹ (realHessian f x) :=
  complexHessianContraction_pairing a b _ hf

/-- Interior regularity suffices; no boundary extension of the inverse is used. -/
theorem strictPsh_realCoefficients_continuousOn (a b : ι → E)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef) (i j : ι ⊕ ι) :
    ContinuousOn (fun x => realLinearizationMatrix (complexHessian a b u x)⁻¹ i j) U := by
  intro x hx
  have hA := complexHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) a b
  have hI := field_inverse_contDiffAt_of_det_ne_zero hA (ne_of_gt (hpos x hx).det_pos)
  exact (realLinearizationMatrix_contDiffAt hI i j).continuousAt.continuousWithinAt

variable [ProperSpace E] [Nontrivial E]

/-- The coefficient C is allowed to depend on the particular touching branch. -/
theorem strictPsh_gradient_local_zero (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U) (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    {x : E} (hx : x ∈ U) (hx0 : f x = 0)
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      complexLinearized a b u f y ≤ c * (f y + ‖fderiv ℝ f y‖)) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  apply continuous_matrix_gradient_local_zero e hU
    (strictPsh_realCoefficients_continuousOn a b hU hu hpos)
    (fun y hy => realLinearizationMatrix_posDef (hpos y hy).inv) hf hnonneg hx hx0
  obtain ⟨c, hc, hest⟩ := hest
  refine ⟨c, hc, ?_⟩
  filter_upwards [hU.mem_nhds hx, hest] with y hy hye
  rw [complexLinearized_eq_real a b u (hf.contDiffAt (hU.mem_nhds hy))] at hye
  simpa only [complexHessianContraction, he] using hye

theorem strictPsh_gradient_strong_minimum_positive (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U) (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    (hest : ∀ x ∈ U, f x = 0 → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      complexLinearized a b u f y ≤ c * (f y + ‖fderiv ℝ f y‖))
    (hanchor : ∃ x ∈ U, 0 < f x) : ∀ x ∈ U, 0 < f x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn hf.continuousOn hnonneg
    (fun x hx hx0 => strictPsh_gradient_local_zero a b e he hU hu hpos hf hnonneg hx hx0
      (hest x hx hx0)) hanchor

end PowerConvexity
